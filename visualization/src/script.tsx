import React, { useState, useEffect, useCallback, useMemo } from "react";
import { createRoot } from "react-dom/client";
import ReactDOMServer from "react-dom/server";
import * as dagre from "@dagrejs/dagre";
import * as Viz from "@viz-js/viz";

import BorrowsAndActions from "./components/BorrowsAndActions";
import {
  computeTableHeight,
  isStorageStmt,
} from "./components/BasicBlockTable";
import {
  BasicBlockData,
  BorrowAction,
  CurrentPoint,
  DagreEdge,
  DagreInputNode,
  DagreNode,
  PathData,
} from "./types";
import Edge from "./components/Edge";
import SymbolicHeap from "./components/SymbolicHeap";
import BasicBlockNode from "./components/BasicBlockNode";
import PathConditions from "./components/PathConditions";
import Assertions, { Assertion } from "./components/Assertions";
import {
  MirGraphEdge,
  MirGraphNode,
  getAssertions,
  getFunctions,
  getGraphData,
  getPathData,
  getPaths,
} from "./api";
import { filterNodesAndEdges } from "./mir_graph";

const layoutSizedNodes = (
  nodes: DagreInputNode<BasicBlockData>[],
  edges: any
) => {
  const g = new dagre.graphlib.Graph().setDefaultEdgeLabel(() => ({}));
  g.setGraph({ ranksep: 100, rankdir: "TB", marginy: 100 });

  edges.forEach((edge: any) => g.setEdge(edge.source, edge.target));
  nodes.forEach((node) => g.setNode(node.id, node));

  dagre.layout(g);

  let height = g.graph().height;
  if (!isFinite(height)) {
    height = null;
  }

  return {
    nodes: nodes as DagreNode<BasicBlockData>[],
    edges,
    height,
  };
};

function toDagreEdges(edges: MirGraphEdge[]): DagreEdge[] {
  return edges.map((edge, idx) => ({
    id: `${edge.source}-${edge.target}-${idx}`,
    source: edge.source,
    target: edge.target,
    data: { label: edge.label },
    type: "straight",
  }));
}

function layoutUnsizedNodes(
  nodes: MirGraphNode[],
  edges: { source: string; target: string }[],
  showStorageStmts: boolean
): {
  nodes: DagreNode<BasicBlockData>[];
  height: number;
} {
  const heightCalculatedNodes = nodes.map((node) => {
    return {
      id: node.id,
      data: {
        block: node.block,
        stmts: node.stmts,
        terminator: node.terminator,
      },
      height: computeTableHeight(node, showStorageStmts),
      width: 300,
    };
  });
  const g = layoutSizedNodes(heightCalculatedNodes, edges);
  return {
    nodes: g.nodes,
    height: g.height,
  };
}

async function main() {
  const viz = await Viz.instance();
  const functions = await getFunctions();
  let initialFunction = localStorage.getItem("selectedFunction");
  if (!initialFunction || !Object.keys(functions).includes(initialFunction)) {
    initialFunction = Object.keys(functions)[0];
  }
  const initialPaths = await getPaths(initialFunction);
  const initialAssertions = await getAssertions(initialFunction);

  let initialPath = 0;
  let initialPathStr = localStorage.getItem("selectedPath");
  if (initialPathStr) {
    initialPath = parseInt(initialPathStr);
    if (initialPath >= initialPaths.length) {
      initialPath = 0;
    }
  } else {
    initialPath = 0;
  }

  const App: React.FC<{}> = () => {
    const [pathData, setPathData] = useState<PathData | null>(null);
    const [currentPoint, setCurrentPoint] = useState<CurrentPoint>({
      block: 0,
      stmt: 0,
    });
    const [selectedFunction, setSelectedFunction] = useState<string>(
      initialFunction || functions[0]
    );
    const [selectedPath, setSelectedPath] = useState<number>(initialPath);
    const [paths, setPaths] = useState<number[][]>(initialPaths);
    const [assertions, setAssertions] =
      useState<Assertion[]>(initialAssertions);
    const [nodes, setNodes] = useState<MirGraphNode[]>([]);
    const [edges, setEdges] = useState<MirGraphEdge[]>([]);
    const [showPathBlocksOnly, setShowPathBlocksOnly] = useState(
      localStorage.getItem("showPathBlocksOnly") === "true"
    );
    const [showUnwindEdges, setShowUnwindEdges] = useState(false);
    const [showPCS, setShowPCS] = useState(
      localStorage.getItem("showPCS") === "true"
    );
    const [showStorageStmts, setShowStorageStmts] = useState(
      localStorage.getItem("showStorageStmts") === "true"
    );

    const { filteredNodes, filteredEdges } = filterNodesAndEdges(nodes, edges, {
      showUnwindEdges,
      path:
        showPathBlocksOnly && selectedPath < paths.length
          ? paths[selectedPath]
          : null,
    });

    const layoutResult = useMemo(() => {
      return layoutUnsizedNodes(filteredNodes, filteredEdges, showStorageStmts);
    }, [filteredNodes, filteredEdges, showStorageStmts]);

    const dagreNodes = layoutResult.nodes;
    const dagreEdges = useMemo(() => {
      return toDagreEdges(filteredEdges);
    }, [filteredEdges]);

    const fetchDotFile = async (filePath: string) => {
      const response = await fetch(filePath);
      return await response.text();
    };

    async function loadPCSDotGraph() {
      const dotFilePath = `data/${selectedFunction}/block_${currentPoint.block}_stmt_${currentPoint.stmt}.dot`;
      const dotData = await fetchDotFile(dotFilePath);
      const dotGraph = document.getElementById("dot-graph");
      if (!dotGraph) {
        console.error("Dot graph element not found");
        return;
      }
      Viz.instance().then(function (viz) {
        dotGraph.innerHTML = "";
        dotGraph.appendChild(viz.renderSVGElement(dotData));
      });
    }

    useEffect(() => {
      const graph = document.getElementById("dot-graph");
      if (showPCS) {
        graph.style.display = "block";
      } else {
        graph.style.display = "none";
      }
    }, [showPCS]);

    useEffect(() => {
      loadPCSDotGraph();
    }, [currentPoint, selectedFunction]);

    useEffect(() => {
      if (selectedFunction) {
        (async function () {
          const mirGraph = await getGraphData(selectedFunction);
          setNodes(mirGraph.nodes);
          setEdges(mirGraph.edges);
          setPaths(await getPaths(selectedFunction));
        })();
      }
    }, [selectedFunction]);

    useEffect(() => {
      const fetchPathData = async () => {
        if (paths.length === 0 || selectedPath >= paths.length) return;

        const currentPath = paths[selectedPath];
        const currentBlockIndex = currentPath.indexOf(currentPoint.block);

        if (currentBlockIndex === -1) {
          setPathData(null);
          return;
        }

        const pathToCurrentBlock = currentPath.slice(0, currentBlockIndex + 1);

        try {
          const data: PathData = await getPathData(
            selectedFunction,
            pathToCurrentBlock,
            currentPoint.stmt
          );
          setPathData(data);
        } catch (error) {
          console.error("Error fetching path data:", error);
        }
      };

      fetchPathData();
    }, [selectedFunction, selectedPath, currentPoint, paths]);

    useEffect(() => {
      const handleKeyDown = (event: KeyboardEvent) => {
        if (
          event.key === "ArrowUp" ||
          event.key === "ArrowDown" ||
          event.key === "j" ||
          event.key === "k"
        ) {
          event.preventDefault(); // Prevent scrolling
          setCurrentPoint((prevPoint) => {
            const currentNode = nodes.find(
              (node) => node.block === prevPoint.block
            );
            if (!currentNode) return prevPoint;

            const isSelectable = (node: { stmts: string[] }, idx: number) => {
              if (showStorageStmts || idx === node.stmts.length) {
                return true;
              } else {
                return !isStorageStmt(node.stmts[idx]);
              }
            };

            const getNextStmtIdx = (
              node: { stmts: string[] },
              from: number
            ) => {
              const offset = direction === "up" ? -1 : 1;
              let idx = from + offset;
              while (idx >= 0 && idx <= node.stmts.length) {
                if (isSelectable(node, idx)) {
                  return idx;
                } else {
                  console.log(
                    `${node.stmts[idx]}[${currentNode.block}:${idx}] is not selectable`
                  );
                }
                idx += offset;
              }
              return null;
            };

            const direction =
              event.key === "ArrowUp" || event.key === "k" ? "up" : "down";

            const nextStmtIdx = getNextStmtIdx(currentNode, prevPoint.stmt);
            if (nextStmtIdx !== null) {
              return { ...prevPoint, stmt: nextStmtIdx };
            } else {
              const currBlockIdx = filteredNodes.findIndex(
                (node) => node.block === prevPoint.block
              );
              if (direction === "down") {
                const nextBlockIdx = (currBlockIdx + 1) % filteredNodes.length;
                const data = filteredNodes[nextBlockIdx];
                return {
                  block: filteredNodes[nextBlockIdx].block,
                  stmt: getNextStmtIdx(data, -1),
                };
              } else {
                const nextBlockIdx =
                  (currBlockIdx - 1 + filteredNodes.length) %
                  filteredNodes.length;
                const data = filteredNodes[nextBlockIdx];
                return {
                  block: data.block,
                  stmt: data.stmts.length,
                };
              }
            }
          });
        } else if (event.key >= "0" && event.key <= "9") {
          const newBlock = parseInt(event.key);
          setCurrentPoint({ block: newBlock, stmt: 0 });
        }
      };

      window.addEventListener("keydown", handleKeyDown);
      return () => {
        window.removeEventListener("keydown", handleKeyDown);
      };
    }, [nodes, showPathBlocksOnly]);

    function addLocalStorageCallback(key: string, value: any) {
      useEffect(() => {
        localStorage.setItem(key, value.toString());
      }, [value]);
    }

    addLocalStorageCallback("selectedFunction", selectedFunction);
    addLocalStorageCallback("selectedPath", selectedPath);
    addLocalStorageCallback("showPathBlocksOnly", showPathBlocksOnly);
    addLocalStorageCallback("showPCS", showPCS);
    addLocalStorageCallback("showStorageStmts", showStorageStmts);

    const isBlockOnSelectedPath = useCallback(
      (block: number) => {
        if (paths.length === 0 || selectedPath >= paths.length) return false;
        return paths[selectedPath].includes(block);
      },
      [paths, selectedPath]
    );

    return (
      <div style={{ position: "relative", minHeight: "100vh" }}>
        <div>
          <label htmlFor="function-select">Select Function:</label>
          <select
            id="function-select"
            value={selectedFunction}
            onChange={async (e) => {
              const fn = e.target.value;
              setSelectedFunction(fn);
            }}
          >
            {Object.keys(functions).map((func) => (
              <option key={func} value={func}>
                {functions[func]}
              </option>
            ))}
          </select>
          <br />
          <label htmlFor="path-select">Select Path:</label>
          <select
            id="path-select"
            value={selectedPath}
            onChange={(e) => setSelectedPath(parseInt(e.target.value))}
          >
            {paths.map((path, index) => (
              <option key={index} value={index}>
                {path.map((p) => `bb${p}`).join(" -> ")}
              </option>
            ))}
          </select>
          <br />
          <label>
            <input
              type="checkbox"
              checked={showPathBlocksOnly}
              onChange={(e) => setShowPathBlocksOnly(e.target.checked)}
            />
            Show path blocks only
          </label>
          <br />
          <label>
            <input
              type="checkbox"
              checked={showPCS}
              onChange={(e) => setShowPCS(e.target.checked)}
            />
            Show PCS
          </label>
          <br />
          <label>
            <input
              type="checkbox"
              checked={showStorageStmts}
              onChange={(e) => setShowStorageStmts(e.target.checked)}
            />
            Show storage statements
          </label>
        </div>
        <div
          className="graph-container"
          style={{ height: layoutResult.height + 100 }}
        >
          <div id="mir-graph">
            {dagreNodes.map((node) => {
              return (
                <BasicBlockNode
                  isOnSelectedPath={isBlockOnSelectedPath(node.data.block)}
                  key={node.id}
                  data={node.data}
                  height={node.height}
                  position={{
                    x: node.x,
                    y: node.y,
                  }}
                  currentPoint={currentPoint}
                  setCurrentPoint={setCurrentPoint}
                  showStorageStmts={showStorageStmts}
                />
              );
            })}
          </div>
          {dagreEdges.map((edge) => (
            <Edge key={edge.id} edge={edge} nodes={dagreNodes} />
          ))}
        </div>
        {pathData && (
          <>
            <div style={{ position: "absolute", top: "20px", right: "20px" }}>
              <SymbolicHeap heap={pathData.heap} />
              <PathConditions pcs={pathData.pcs} />
              <Assertions assertions={assertions} />
            </div>
            {/* <BorrowsAndActions pathData={pathData} /> */}
          </>
        )}
      </div>
    );
  };

  const rootElement = document.getElementById("root");
  if (rootElement) {
    const root = createRoot(rootElement);
    root.render(<App />);
  }
}

main();

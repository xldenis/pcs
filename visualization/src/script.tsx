import React, { useState, useEffect, useCallback, useMemo } from "react";
import { createRoot } from "react-dom/client";
import ReactDOMServer from "react-dom/server";
import * as dagre from "@dagrejs/dagre";
import * as Viz from "@viz-js/viz";

import BorrowsAndActions from "./components/BorrowsAndActions";
import BasicBlockTable, {
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

const fetchJsonFile = async (filePath: string) => {
  const response = await fetch(filePath);
  return await response.json();
};

type MirGraphNode = {
  id: string;
  block: number;
  stmts: string[];
  terminator: string;
};

type MirGraphEdge = {
  source: string;
  target: string;
  label: string;
};

type MirGraph = {
  nodes: MirGraphNode[];
  edges: MirGraphEdge[];
};

const layoutSizedNodes = (
  nodes: DagreInputNode<BasicBlockData>[],
  edges: any
) => {
  const g = new dagre.graphlib.Graph().setDefaultEdgeLabel(() => ({}));
  g.setGraph({ ranksep: 100, rankdir: "TB", marginy: 100 });

  edges.forEach((edge: any) => g.setEdge(edge.source, edge.target));
  nodes.forEach((node) => g.setNode(node.id, node));

  dagre.layout(g);

  return {
    nodes: nodes as DagreNode<BasicBlockData>[],
    edges,
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
): DagreNode<BasicBlockData>[] {
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
  return g.nodes;
}

async function getGraphData(func: string): Promise<MirGraph> {
  const graphFilePath = `data/${func}/mir.json`;
  return await fetchJsonFile(graphFilePath);
}

async function getFunctions(): Promise<Record<string, string>> {
  return await fetchJsonFile("data/functions.json");
}

const getPaths = async (functionName: string) => {
  try {
    const paths: number[][] = await fetchJsonFile(
      `data/${functionName}/paths.json`
    );
    return paths;
  } catch (error) {
    return [];
  }
};

async function main() {
  const viz = await Viz.instance();
  const functions = await getFunctions();
  let initialFunction = localStorage.getItem("selectedFunction");
  if (!initialFunction || !Object.keys(functions).includes(initialFunction)) {
    initialFunction = Object.keys(functions)[0];
  }
  const initialPaths = await getPaths(initialFunction);

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
    const [nodes, setNodes] = useState<DagreNode<BasicBlockData>[]>([]);
    const [edges, setEdges] = useState<DagreEdge[]>([]);
    const [showPathBlocksOnly, setShowPathBlocksOnly] = useState(false);
    const [graphHeight, setGraphHeight] = useState(800);
    const [showPCS, setShowPCS] = useState(true);
    const [showStorageStmts, setShowStorageStmts] = useState(true);

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
          const edges = toDagreEdges(mirGraph.edges);
          const nodes = layoutUnsizedNodes(
            mirGraph.nodes,
            edges,
            showStorageStmts
          );
          setNodes(nodes);
          setEdges(edges);
          setPaths(await getPaths(selectedFunction));
        })();
      }
    }, [selectedFunction]);

    useEffect(() => {
      if (nodes.length > 0 && edges.length > 0) {
        const { filteredNodes, filteredEdges } = filterNodesAndEdges();
        const { nodes: layoutedNodes } = layoutSizedNodes(
          filteredNodes,
          filteredEdges
        );

        // Update positions of visible nodes, keep others unchanged
        setNodes(
          nodes.map((node) => {
            const layoutedNode = layoutedNodes.find((n) => n.id === node.id);
            if (layoutedNode) {
              return { ...node, x: layoutedNode.x, y: layoutedNode.y };
            }
            return node;
          })
        );
      }
    }, [showPathBlocksOnly, selectedPath]);

    useEffect(() => {
      const fetchHeapData = async () => {
        if (paths.length === 0 || selectedPath >= paths.length) return;

        const currentPath = paths[selectedPath];
        const currentBlockIndex = currentPath.indexOf(currentPoint.block);

        if (currentBlockIndex === -1) return;

        const pathToCurrentBlock = currentPath.slice(0, currentBlockIndex + 1);
        const heapFilePath = `data/${selectedFunction}/path_${pathToCurrentBlock.map((block) => `bb${block}`).join("_")}_stmt_${currentPoint.stmt}.json`;

        try {
          const data: PathData = await fetchJsonFile(heapFilePath);
          setPathData(data);
        } catch (error) {
          console.error("Error fetching path data:", error);
        }
      };

      fetchHeapData();
    }, [selectedFunction, selectedPath, currentPoint, paths]);

    const filterNodesAndEdges = () => {
      if (!showPathBlocksOnly || paths.length === 0) {
        return { filteredNodes: nodes, filteredEdges: edges };
      }

      const currentPath = paths[selectedPath];
      const filteredNodes = nodes.filter((node) =>
        currentPath.includes(node.data.block)
      );
      const filteredEdges = edges.filter((edge) => {
        const sourceNode = nodes.find((n) => n.id === edge.source);
        const targetNode = nodes.find((n) => n.id === edge.target);
        return (
          sourceNode &&
          targetNode &&
          currentPath.includes(sourceNode.data.block) &&
          currentPath.includes(targetNode.data.block)
        );
      });

      return { filteredNodes, filteredEdges };
    };

    const { filteredNodes, filteredEdges } = filterNodesAndEdges();

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
              (node) => node.data.block === prevPoint.block
            );
            if (!currentNode) return prevPoint;

            const stmtCount = currentNode.data.stmts.length + 1;

            const isSelectable = (node: BasicBlockData, idx: number) => {
              if (showStorageStmts || idx === stmtCount - 1) {
                return true;
              } else {
                return !isStorageStmt(node.stmts[idx]);
              }
            };

            const getNextStmtIdx = (node: BasicBlockData, from: number) => {
              const offset = direction === "up" ? -1 : 1;
              let idx = from + offset;
              while (idx >= 0 && idx < stmtCount) {
                if (isSelectable(node, idx)) {
                  return idx;
                } else {
                  console.log(
                    `${currentNode.data.stmts[idx]}[${currentNode.data.block}:${idx}] is not selectable`
                  );
                }
                idx += offset;
              }
              return null;
            };

            const direction =
              event.key === "ArrowUp" || event.key === "k" ? "up" : "down";

            const nextStmtIdx = getNextStmtIdx(
              currentNode.data,
              prevPoint.stmt
            );
            if (nextStmtIdx !== null) {
              return { ...prevPoint, stmt: nextStmtIdx };
            } else {
              const currBlockIdx = filteredNodes.findIndex(
                (node) => node.data.block === prevPoint.block
              );
              if (direction === "down") {
                const nextBlockIdx = (currBlockIdx + 1) % filteredNodes.length;
                const data = filteredNodes[nextBlockIdx].data;
                return {
                  block: filteredNodes[nextBlockIdx].data.block,
                  stmt: getNextStmtIdx(data, -1),
                };
              } else {
                const nextBlockIdx =
                  (currBlockIdx - 1 + filteredNodes.length) %
                  filteredNodes.length;
                const data = filteredNodes[nextBlockIdx].data;
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

    useEffect(() => {
      if (nodes.length > 0) {
        const maxY = Math.max(...nodes.map((node) => node.y + node.height));
        setGraphHeight(maxY + 100); // Add some padding
      }
    }, [nodes]);

    useEffect(() => {
      localStorage.setItem("selectedFunction", selectedFunction);
    }, [selectedFunction]);

    useEffect(() => {
      localStorage.setItem("selectedPath", selectedPath.toString());
    }, [selectedPath]);

    useEffect(() => {
      const resizedNodes = layoutUnsizedNodes(
        nodes.map((node) => ({
          id: node.id,
          block: node.data.block,
          stmts: node.data.stmts,
          terminator: node.data.terminator,
        })),
        edges,
        showStorageStmts
      );
      setNodes(resizedNodes);
    }, [showStorageStmts]);

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
        <div className="graph-container" style={{ height: graphHeight }}>
          <div id="mir-graph">
            {filteredNodes.map((node) => {
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
          {filteredEdges.map((edge) => (
            <Edge key={edge.id} edge={edge} nodes={filteredNodes} />
          ))}
        </div>
        {pathData && (
          <>
            <SymbolicHeap heap={pathData.heap} />
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

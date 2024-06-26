import React, { useState, useEffect, useCallback, useMemo } from "react";
import { createRoot } from "react-dom/client";
import ReactDOMServer from "react-dom/server";
import * as dagre from "@dagrejs/dagre";
import * as Viz from "@viz-js/viz";

import { BasicBlockData, DagreInputNode, DagreNode } from "./types";
import Edge from "./components/Edge";
import SymbolicHeap from "./components/SymbolicHeap";

type CurrentPoint = {
  block: number;
  stmt: number;
};

const fetchJsonFile = async (filePath: string) => {
  const response = await fetch(filePath);
  return await response.json();
};

type GraphData = {
  initialNodes: {
    id: string;
    data: { block: number; stmts: string[]; terminator: string };
  }[];
  initialEdges: {
    id: string;
    source: string;
    target: string;
    data: { label: string };
  }[];
};

async function getGraphData(func: string): Promise<GraphData> {
  const graphFilePath = `data/${func}/mir.json`;
  const graph: {
    nodes: { id: string; block: number; stmts: string[]; terminator: string }[];
    edges: { source: string; target: string; label: string }[];
  } = await fetchJsonFile(graphFilePath);

  const initialNodes = graph.nodes.map((node) => {
    const container = document.createElement("div");
    container.innerHTML = ReactDOMServer.renderToString(
      BasicBlockTable({
        isOnSelectedPath: false,
        currentPoint: { block: 0, stmt: 0 },
        data: {
          block: node.block,
          stmts: node.stmts,
          terminator: node.terminator,
        },
        setCurrentPoint: () => {},
      })
    );
    document.body.appendChild(container);
    const height = container.offsetHeight;
    container.remove();
    return {
      id: node.id,
      data: {
        block: node.block,
        stmts: node.stmts,
        terminator: node.terminator,
      },
      width: 300,
      height,
    };
  });

  const initialEdges = graph.edges.map((edge, idx) => ({
    id: `${edge.source}-${edge.target}-${idx}`,
    source: edge.source,
    target: edge.target,
    data: {
      label: edge.label,
    },
    type: "straight",
  }));

  return { initialNodes, initialEdges };
}

async function getFunctions(): Promise<Record<string, string>> {
  return await fetchJsonFile("data/functions.json");
}

const layout = (
  nodes: DagreInputNode<BasicBlockData>[],
  edges: any,
  options: any
) => {
  const g = new dagre.graphlib.Graph().setDefaultEdgeLabel(() => ({}));
  g.setGraph({ ranksep: 100, rankdir: options.direction, marginy: 100 });

  edges.forEach((edge: any) => g.setEdge(edge.source, edge.target));
  nodes.forEach((node) => g.setNode(node.id, node));

  dagre.layout(g);

  return {
    nodes: nodes as DagreNode<BasicBlockData>[],
    edges,
  };
};

function BasicBlockNode({
  height,
  data,
  currentPoint,
  position,
  setCurrentPoint,
  isOnSelectedPath,
}: {
  height: number;
  data: BasicBlockData;
  currentPoint: CurrentPoint;
  position: { x: number; y: number };
  setCurrentPoint: (point: CurrentPoint) => void;
  isOnSelectedPath: boolean;
}) {
  return (
    <div
      style={{
        position: "absolute",
        left: position.x,
        top: position.y - height / 2,
      }}
    >
      <BasicBlockTable
        data={data}
        currentPoint={currentPoint}
        setCurrentPoint={setCurrentPoint}
        isOnSelectedPath={isOnSelectedPath}
      />
    </div>
  );
}

function BasicBlockTable({
  data,
  currentPoint,
  setCurrentPoint,
  isOnSelectedPath,
}: {
  data: BasicBlockData;
  currentPoint: CurrentPoint;
  setCurrentPoint: (point: CurrentPoint) => void;
  isOnSelectedPath: boolean;
}) {
  return (
    <table
      cellSpacing={0}
      cellPadding={4}
      style={{
        borderCollapse: "collapse",
        width: "300px",
        border: isOnSelectedPath ? "5px solid red" : "1px solid black",
      }}
    >
      <tbody>
        <tr>
          <td>(on start)</td>
          <td>
            <b>bb{data.block}</b>
          </td>
        </tr>
        {data.stmts.map((stmt, i) => (
          <tr
            className={
              i === currentPoint.stmt && data.block === currentPoint.block
                ? "highlight"
                : ""
            }
            key={i}
            onClick={() => setCurrentPoint({ block: data.block, stmt: i })}
          >
            <td>{i}</td>
            <td>
              <code>{stmt}</code>
            </td>
          </tr>
        ))}
        <tr>
          <td>T</td>
          <td>
            <code>{data.terminator}</code>
          </td>
        </tr>
      </tbody>
    </table>
  );
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
    const [heapData, setHeapData] = useState<Record<string, string>>({});
    const [currentPoint, setCurrentPoint] = useState<CurrentPoint>({
      block: 0,
      stmt: 0,
    });
    const [selectedFunction, setSelectedFunction] = useState<string>(
      initialFunction || functions[0]
    );
    const [selectedPath, setSelectedPath] = useState<number>(initialPath);
    const [paths, setPaths] = useState<number[][]>(initialPaths);
    const [nodes, setNodes] = useState([]);
    const [edges, setEdges] = useState([]);
    const [showPathBlocksOnly, setShowPathBlocksOnly] = useState(false);
    const [graphHeight, setGraphHeight] = useState(800); // Default height

    const fetchDotFile = async (filePath: string) => {
      const response = await fetch(filePath);
      return await response.text();
    };

    async function loadDotGraph() {
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
      loadDotGraph();
    }, [currentPoint, selectedFunction]);

    useEffect(() => {
      if (selectedFunction) {
        (async function () {
          const graphData = await getGraphData(selectedFunction);
          const { nodes, edges } = layout(
            graphData.initialNodes,
            graphData.initialEdges,
            { direction: "TB" }
          );
          console.log(nodes);
          setNodes(nodes);
          setEdges(edges);
          setPaths(await getPaths(selectedFunction));
        })();
      }
    }, [selectedFunction]);

    useEffect(() => {
      if (nodes.length > 0 && edges.length > 0) {
        const { filteredNodes, filteredEdges } = filterNodesAndEdges();
        const { nodes: layoutedNodes } = layout(filteredNodes, filteredEdges, {
          direction: "TB",
        });

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
          const data = await fetchJsonFile(heapFilePath);
          setHeapData(data);
        } catch (error) {
          console.error("Error fetching heap data:", error);
          setHeapData({});
        }
      };

      fetchHeapData();
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
              (node) => node.data.block === prevPoint.block
            );
            if (!currentNode) return prevPoint;

            const stmtCount = currentNode.data.stmts.length;
            let newStmt = prevPoint.stmt;

            if (event.key === "ArrowUp" || event.key === "k") {
              newStmt = (newStmt - 1 + stmtCount) % stmtCount;
            } else if (event.key === "ArrowDown" || event.key === "j") {
              newStmt = (newStmt + 1) % stmtCount;
            }

            return { ...prevPoint, stmt: newStmt };
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
    }, [nodes]);

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
        </div>
        <div className="graph-container" style={{ height: graphHeight }}>
          <div id="mir-graph">
            {filteredNodes.map((node) => (
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
              />
            ))}
          </div>
          {filteredEdges.map((edge) => (
            <Edge key={edge.id} edge={edge} nodes={filteredNodes} />
          ))}
        </div>
        <SymbolicHeap heap={heapData} />
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

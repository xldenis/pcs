import React, { useState, useEffect, useCallback, useMemo } from "react";
import { createRoot } from "react-dom/client";
import ReactDOMServer from "react-dom/server";
import * as dagre from "@dagrejs/dagre";
import * as Viz from "@viz-js/viz";

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

async function getFunctions(): Promise<string[]> {
  return await fetchJsonFile("data/functions.json");
}

const layout = (
  nodes: DagreInputNode<BasicBlockData>[],
  edges: any,
  options: any
) => {
  const g = new dagre.graphlib.Graph().setDefaultEdgeLabel(() => ({}));
  g.setGraph({ ranksep: 100, rankdir: options.direction });

  edges.forEach((edge: any) => g.setEdge(edge.source, edge.target));
  nodes.forEach((node) => g.setNode(node.id, node));

  dagre.layout(g);

  return {
    nodes: nodes as DagreNode<BasicBlockData>[],
    edges,
  };
};

type BasicBlockData = { block: number; stmts: string[]; terminator: string };

function Edge({
  edge,
  nodes,
}: {
  edge: any;
  nodes: DagreNode<BasicBlockData>[];
}) {
  const sourceNode = nodes.find((n) => n.id === edge.source);
  const targetNode = nodes.find((n) => n.id === edge.target);

  if (!sourceNode || !targetNode) return null;

  const startX = sourceNode.x + sourceNode.width / 2;
  const startY = sourceNode.y + sourceNode.height;
  const endX = targetNode.x + targetNode.width / 2;
  const endY = targetNode.y;

  return (
    <svg
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: "100%",
        height: "100%",
        pointerEvents: "none",
      }}
    >
      <line
        x1={startX}
        y1={startY}
        x2={endX}
        y2={endY}
        stroke="black"
        strokeWidth={2}
      />
      {edge.data.label && (
        <text
          x={(startX + endX) / 2}
          y={(startY + endY) / 2}
          textAnchor="middle"
          alignmentBaseline="middle"
          fill="black"
          fontSize="12"
        >
          {edge.data.label}
        </text>
      )}
    </svg>
  );
}

function BasicBlockNode({
  data,
  currentPoint,
  position,
  setCurrentPoint,
}: {
  data: BasicBlockData;
  currentPoint: CurrentPoint;
  position: { x: number; y: number };
  setCurrentPoint: (point: CurrentPoint) => void;
}) {
  return (
    <div style={{ position: "absolute", left: position.x, top: position.y }}>
      <BasicBlockTable
        data={data}
        currentPoint={currentPoint}
        setCurrentPoint={setCurrentPoint}
      />
    </div>
  );
}

function BasicBlockTable({
  data,
  currentPoint,
  setCurrentPoint,
}: {
  data: BasicBlockData;
  currentPoint: CurrentPoint;
  setCurrentPoint: (point: CurrentPoint) => void;
}) {
  return (
    <table
      border={1}
      cellSpacing={0}
      cellPadding={4}
      style={{ borderCollapse: "collapse", width: "300px" }}
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

type DagreInputNode<T> = {
  id: string;
};

type DagreNode<T> = {
  id: string;
  data: T;
  x: number;
  y: number;
  width: number;
  height: number;
};

function SymbolicHeap({ heap }: { heap: Record<string, string> }) {
  return (
    <table
      style={{
        borderCollapse: "collapse",
        width: "300px",
        position: "absolute",
        top: "20px",
        right: "20px",
        backgroundColor: "white",
        boxShadow: "0 0 10px rgba(0,0,0,0.1)",
      }}
    >
      <thead>
        <tr>
          <th
            style={{
              border: "1px solid black",
              padding: "8px",
              backgroundColor: "#f2f2f2",
            }}
          >
            Location
          </th>
          <th
            style={{
              border: "1px solid black",
              padding: "8px",
              backgroundColor: "#f2f2f2",
            }}
          >
            Value
          </th>
        </tr>
      </thead>
      <tbody>
        {Object.entries(heap).map(([symbol, value]) => (
          <tr key={symbol}>
            <td style={{ border: "1px solid black", padding: "8px" }}>
              <code>{symbol}</code>
            </td>
            <td style={{ border: "1px solid black", padding: "8px" }}>
              <code>{value}</code>
            </td>
          </tr>
        ))}
      </tbody>
    </table>
  );
}

async function main() {
  const viz = await Viz.instance();
  const functions = await getFunctions();

  const App: React.FC<{}> = () => {
    const [heapData, setHeapData] = useState<Record<string, string>>({});
    const [currentPoint, setCurrentPoint] = useState<CurrentPoint>({
      block: 0,
      stmt: 0,
    });
    const [selectedFunction, setSelectedFunction] = useState<string>(
      functions[0]
    );
    const [selectedPath, setSelectedPath] = useState<number>(0);
    const [paths, setPaths] = useState<number[][]>([]);
    const [nodes, setNodes] = useState([]);
    const [edges, setEdges] = useState([]);
    const [showPathBlocksOnly, setShowPathBlocksOnly] = useState(false);

    const fetchDotFile = async (filePath: string) => {
      const response = await fetch(filePath);
      return await response.text();
    };

    const getPaths = async (functionName: string) => {
      const paths: number[][] = await fetchJsonFile(
        `data/${functionName}/paths.json`
      );
      return paths;
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
            {functions.map((func) => (
              <option key={func} value={func}>
                {func}
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
        <div className="graph-container" style={{ height: 800 }}>
          <div id="mir-graph">
            {filteredNodes.map((node) => (
              <BasicBlockNode
                key={node.id}
                data={node.data}
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

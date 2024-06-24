import React, { useState, useEffect, useCallback, useMemo } from "react";
import { createRoot } from "react-dom/client";
import ReactDOMServer from "react-dom/server";
import * as dagre from "@dagrejs/dagre";
import * as Viz from "@viz-js/viz";
import "reactflow/dist/style.css";

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

async function main() {
  const functions = await getFunctions();

  const App: React.FC<{}> = () => {
    const [currentPoint, setCurrentPoint] = useState<CurrentPoint>({
      block: 0,
      stmt: 0,
    });
    const [selectedFunction, setSelectedFunction] = useState<string>(
      functions[0]
    );
    const [selectedPath, setSelectedPath] = useState<number>(0);
    const [paths, setPaths] = useState<number[][]>([]);
    const [dotData, setDotData] = useState<string | null>();
    const [nodes, setNodes] = useState([]);
    const [edges, setEdges] = useState([]);

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
        }
      };

      window.addEventListener("keydown", handleKeyDown);
      return () => {
        window.removeEventListener("keydown", handleKeyDown);
      };
    }, [nodes]);

    return (
      <div>
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
        </div>
        <div className="graph-container" style={{ height: 800 }}>
          <div id="mir-graph">
            {nodes.map((node) => (
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
          {edges.map((edge) => (
            <Edge key={edge.id} edge={edge} nodes={nodes} />
          ))}
          <div id="dot-graph"></div>
        </div>
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

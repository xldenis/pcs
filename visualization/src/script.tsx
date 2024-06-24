import ReactFlow, {
  Node,
  Edge,
  useReactFlow,
  useNodesState,
  useEdgesState,
  Panel,
  ReactFlowProvider,
} from "reactflow";
import React, { useState, useEffect, useCallback } from "react";
import { createRoot } from "react-dom/client";
import * as d3 from "d3";
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
    data: { label: string };
    position: { x: number; y: number };
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
    nodes: { id: string; label: string }[];
    edges: { source: string; target: string; label: string }[];
  } = await fetchJsonFile(graphFilePath);

  const initialNodes = graph.nodes.map((node) => ({
    id: node.id,
    data: {
      label: "hi",
    },
    position: {
      x: 0,
      y: 0,
    },
  }));

  const initialEdges = graph.edges.map((edge, idx) => ({
    id: `${edge.source}-${edge.target}-${idx}`,
    source: edge.source,
    target: edge.target,
    data: {
      label: edge.label,
    },
  }));

  return { initialNodes, initialEdges };
}

async function getFunctions(): Promise<string[]> {
  return await fetchJsonFile("data/functions.json");
}

async function main() {
  const functions = await getFunctions();

  const renderGraph = (graphData: GraphData) => {
    const g = new dagre.graphlib.Graph().setDefaultEdgeLabel(() => ({}));

    const getLayoutedElements = (nodes: any, edges: any, options: any) => {
      g.setGraph({ rankdir: options.direction });

      edges.forEach((edge: any) => g.setEdge(edge.source, edge.target));
      nodes.forEach((node: any) => g.setNode(node.id, node));

      dagre.layout(g);

      return {
        nodes: nodes.map((node: any) => {
          const position = g.node(node.id);
          // We are shifting the dagre node position (anchor=center center) to the top left
          // so it matches the React Flow node anchor point (top left).
          const x = position.x - node.width / 2;
          const y = position.y - node.height / 2;

          return { ...node, position: { x, y } };
        }),
        edges,
      };
    };

    const l1 = getLayoutedElements(
      graphData.initialNodes,
      graphData.initialEdges,
      { direction: "TB" }
    );

    const initialNodes = l1.nodes;
    const initialEdges = l1.edges;
    console.log(initialNodes);

    const LayoutFlow = () => {
      const { fitView } = useReactFlow();
      const [nodes, setNodes, onNodesChange] = useNodesState(
        initialNodes
      );
      const [edges, setEdges, onEdgesChange] = useEdgesState(
        initialEdges
      );

      const onLayout = useCallback(
        (direction: string) => {
          const layouted = getLayoutedElements(nodes, edges, { direction });

          setNodes([...layouted.nodes]);
          setEdges([...layouted.edges]);

          window.requestAnimationFrame(() => {
            fitView();
          });
        },
        [nodes, edges]
      );

      return (
        <ReactFlow
          nodes={nodes}
          edges={edges}
          onNodesChange={onNodesChange}
          onEdgesChange={onEdgesChange}
          onInit={() => onLayout("TB")}
        >
          <Panel position="top-right">
            <button onClick={() => onLayout("TB")}>vertical layout</button>
            <button onClick={() => onLayout("LR")}>horizontal layout</button>
          </Panel>
        </ReactFlow>
      );
    };

    return (
      <ReactFlowProvider>
        <LayoutFlow />
      </ReactFlowProvider>
    );
  };

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
    const [graphData, setGraphData] = useState<GraphData | null>();
    const [dotData, setDotData] = useState<string | null>();

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
          setGraphData(await getGraphData(selectedFunction));
          setPaths(await getPaths(selectedFunction));
        })();
      }
    }, [selectedFunction]);

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
          {graphData && renderGraph(graphData)}
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

import { MirGraphEdge, MirGraphNode } from "./api";
import { BasicBlockData, DagreEdge, DagreNode } from "./types";

export type FilterOptions = {
  showUnwindEdges: boolean;
  path: number[] | null;
};

export function filterNodesAndEdges(
  nodes: MirGraphNode[],
  edges: MirGraphEdge[],
  options: FilterOptions
): {
  filteredNodes: MirGraphNode[];
  filteredEdges: MirGraphEdge[];
} {
  let filteredNodes = nodes;
  let filteredEdges = edges;
  if (!options.showUnwindEdges) {
    filteredNodes = nodes.filter((node) => node.terminator !== "resume");
    filteredEdges = edges.filter((edge) => edge.label !== "unwind");
  }
  if (options.path) {
    filteredNodes = filteredNodes.filter((node) =>
      options.path.includes(node.block)
    );
    filteredEdges = filteredEdges.filter((edge) => {
      const sourceNode = nodes.find((n) => n.id === edge.source);
      const targetNode = nodes.find((n) => n.id === edge.target);
      return (
        sourceNode &&
        targetNode &&
        options.path.includes(sourceNode.block) &&
        options.path.includes(targetNode.block)
      );
    });
  }

  return { filteredNodes, filteredEdges };
}

import React from "react";
import type { BasicBlockData, DagreNode } from "../types";

export default function Edge({
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

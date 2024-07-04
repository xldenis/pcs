import React from "react";
import Table from "./Table";
export default function SymbolicHeap({
  heap,
}: {
  heap: Record<string, string>;
}) {
  return (
    <Table
      columns={["Location", "Value"]}
      data={Object.entries(heap).map(([symbol, value]) => [symbol, value])}
    />
  );
}

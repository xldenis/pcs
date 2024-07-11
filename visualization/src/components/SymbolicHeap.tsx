import React from "react";
import Table from "./Table";
export default function SymbolicHeap({
  heap,
}: {
  heap: Record<string, { value: string; ty: string }>;
}) {
  return (
    <Table
      columns={["Location", "Value", "Type"]}
      data={Object.entries(heap).map(([symbol, value]) => [
        symbol,
        value.value,
        value.ty,
      ])}
    />
  );
}

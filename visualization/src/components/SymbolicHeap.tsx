import React from "react";
export default function SymbolicHeap({ heap }: { heap: Record<string, string> }) {
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

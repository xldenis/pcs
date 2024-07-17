import React from "react";

export type Selection = "before_start" | "before_after" | "start" | "after";

export function PCSGraphSelector({
  selected,
  onSelect,
}: {
  selected: Selection;
  onSelect: (selection: Selection) => void;
}) {
  const names = [
    { key: "before_start", name: "Before Start" },
    { key: "before_after", name: "Before After" },
    { key: "start", name: "Start" },
    { key: "after", name: "After" },
  ];
  return (
    <div style={{ position: "fixed", right: "50px", top: "20px" }}>
      {names.map(({ key, name }) => (
        <div
          key={key}
          style={{
            border: "1px solid #000",
            padding: "10px",
            backgroundColor: selected === key ? "lightgreen" : "transparent",
            cursor: "pointer"
          }}
          onClick={() => onSelect(key as Selection)}
        >
          {name}
        </div>
      ))}
    </div>
  );
}

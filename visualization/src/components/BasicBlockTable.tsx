import React from "react";
import { BasicBlockData, CurrentPoint } from "../types";
import ReactDOMServer from "react-dom/server";

interface BasicBlockTableProps {
  data: BasicBlockData;
  currentPoint: CurrentPoint;
  setCurrentPoint: (point: CurrentPoint) => void;
  isOnSelectedPath: boolean;
  showStorageStmts: boolean;
}

export function isStorageStmt(stmt: string) {
  return stmt.startsWith("StorageLive") || stmt.startsWith("StorageDead");
}

export default function BasicBlockTable({
  data,
  currentPoint,
  setCurrentPoint,
  isOnSelectedPath,
  showStorageStmts,
}: BasicBlockTableProps) {
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
        {data.stmts.map((stmt, i) => {
          if (!showStorageStmts && isStorageStmt(stmt)) {
            return null;
          }
          return (
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
          );
        })}
        <tr
          className={
            currentPoint.stmt == data.stmts.length &&
            data.block === currentPoint.block
              ? "highlight"
              : ""
          }
          onClick={() =>
            setCurrentPoint({ block: data.block, stmt: data.stmts.length })
          }
        >
          <td>T</td>
          <td>
            <code>{data.terminator}</code>
          </td>
        </tr>
      </tbody>
    </table>
  );
}

export function computeTableHeight(
  data: BasicBlockData,
  showStorageStmts: boolean
): number {
  const container = document.createElement("div");
  container.innerHTML = ReactDOMServer.renderToString(
    BasicBlockTable({
      isOnSelectedPath: false,
      currentPoint: { block: 0, stmt: 0 },
      data: {
        block: data.block,
        stmts: data.stmts,
        terminator: data.terminator,
      },
      setCurrentPoint: () => {},
      showStorageStmts,
    })
  );
  document.body.appendChild(container);
  const height = container.offsetHeight;
  container.remove();
  return height;
}

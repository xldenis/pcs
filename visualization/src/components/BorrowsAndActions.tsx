import React from "react";
import { PathData, Borrow, BorrowAction } from "../types";

function BorrowDisplay({ borrow }: { borrow: Borrow }) {
  return (
    <div>
      <p>Assigned: {borrow?.assigned_place?.place}</p>
      <p>Borrowed: {borrow?.borrowed_place?.place}</p>
      <p>Is Mutable: {borrow?.is_mut ? "Yes" : "No"}</p>
      <p>Kind: {borrow?.kind}</p>
    </div>
  );
}

function BorrowActionDisplay({ action }: { action: BorrowAction }) {
  return (
    <div>
      <p>Action: {action.action}</p>
      <BorrowDisplay borrow={action.borrow} />
    </div>
  );
}

export default function BorrowsAndActions({ pathData }: { pathData: PathData }) {
  return (
    <div
      style={{
        position: "fixed",
        bottom: "20px",
        right: "20px",
        backgroundColor: "white",
        boxShadow: "0 0 10px rgba(0,0,0,0.1)",
        padding: "10px",
        maxWidth: "300px",
        overflowY: "auto",
        maxHeight: "80vh",
      }}
    >
      <h3>Borrows and Actions</h3>
      <h4>Borrow Actions (Start)</h4>
      {pathData.borrow_actions_start.map((action, index) => (
        <BorrowActionDisplay key={`start-${index}`} action={action} />
      ))}
      <h4>Borrow Actions (Mid)</h4>
      {pathData.borrow_actions_mid.map((action, index) => (
        <BorrowActionDisplay key={`mid-${index}`} action={action} />
      ))}
      <h4>Current Borrows</h4>
      {pathData.borrows.borrows.map((borrow, index) => (
        <BorrowDisplay key={index} borrow={borrow} />
      ))}
      <h4>Repacks (Start)</h4>
      <ul>
        {pathData.repacks_start.map((repack, index) => (
          <li key={`start-${index}`}>{repack}</li>
        ))}
      </ul>
      <h4>Repacks (Middle)</h4>
      <ul>
        {pathData.repacks_middle.map((repack, index) => (
          <li key={`mid-${index}`}>{repack}</li>
        ))}
      </ul>
    </div>
  );
}

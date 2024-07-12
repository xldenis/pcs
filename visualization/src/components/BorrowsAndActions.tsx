import React from "react";
import {
  PathData,
  Borrow,
  BorrowAction,
  Reborrow,
  ReborrowAction,
  MaybeOldPlace,
} from "../types";

function ReborrowDisplay({ reborrow }: { reborrow: Reborrow }) {
  return (
    <div>
      <p>Assigned Place: {reborrow?.assigned_place?.place}</p>
      <p>Blocked Place: {reborrow?.blocked_place?.place}</p>
      <p>Mutable: {reborrow?.is_mut ? "Yes" : "No"}</p>
    </div>
  );
}

function ReborrowEC({ place }: { place: MaybeOldPlace }) {
  return (
    <div>
      <p>Place: {place.place}</p>
    </div>
  );
}

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

function ReborrowActionDisplay({ action }: { action: ReborrowAction }) {
  return (
    <div>
      <p>Action: {action.action}</p>
      {(action.action === "AddReborrow" ||
        action.action === "RemoveReborrow") && (
        <ReborrowDisplay reborrow={action.reborrow} />
      )}
      {action.action === "ExpandPlace" && <ReborrowEC place={action.place} />}
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

export default function PCSActions({ pathData }: { pathData: PathData }) {
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
      <h4>Borrow Actions (Start)</h4>
      {pathData.borrow_actions_start.map((action, index) => (
        <BorrowActionDisplay key={`start-${index}`} action={action} />
      ))}
      <h4>Borrow Actions (Mid)</h4>
      {pathData.borrow_actions_mid.map((action, index) => (
        <BorrowActionDisplay key={`mid-${index}`} action={action} />
      ))}
      <h4>Reborrow Actions (Start)</h4>
      {pathData.reborrow_actions_start.map((action, index) => (
        <ReborrowActionDisplay key={`start-${index}`} action={action} />
      ))}
      <h4>Reborrow Actions (Mid)</h4>
      {pathData.reborrow_actions_mid.map((action, index) => (
        <ReborrowActionDisplay key={`mid-${index}`} action={action} />
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

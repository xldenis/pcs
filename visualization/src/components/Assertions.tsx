import React from "react";
import Table from "./Table";

function formatAssertion(assertion: string, pcs: string[]) {
  const baseLhs = pcs.join(" && ");
  if (assertion === "false") {
    return `!(${baseLhs})`;
  }
  return pcs.length === 1
    ? `${baseLhs} => ${assertion}`
    : `(${baseLhs}) => ${assertion}`;
}

export type Assertion = {
  assertion: string;
  pcs: string[];
};
export default function Assertions({
  assertions,
}: {
  assertions: Assertion[];
}) {
  return (
    <Table
      columns={["Assertions"]}
      data={assertions.map((assertion) => [
        formatAssertion(assertion.assertion, assertion.pcs),
      ])}
    />
  );
}

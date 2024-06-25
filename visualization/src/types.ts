export type BasicBlockData = {
  block: number;
  stmts: string[];
  terminator: string;
};

export type DagreInputNode<T> = {
  id: string;
};

export type DagreNode<T> = {
  id: string;
  data: T;
  x: number;
  y: number;
  width: number;
  height: number;
};

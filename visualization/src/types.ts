export type CurrentPoint = {
  block: number;
  stmt: number;
};

export type BasicBlockData = {
  block: number;
  stmts: string[];
  terminator: string;
};

export type DagreInputNode<T> = {
  id: string;
};

export type DagreEdge = {
  id: string,
  source: string;
  target: string;
  data: {
    label: string;
  };
  type: string
};

export type DagreNode<T> = {
  id: string;
  data: T;
  x: number;
  y: number;
  width: number;
  height: number;
};

export type MaybeOldPlace = {
  place: string;
  before?: string;
};

export type Borrow = {
  assigned_place: MaybeOldPlace;
  borrowed_place: MaybeOldPlace;
  is_mut: boolean;
  kind: string;
};

export type BorrowAction = {
  action: "AddBorrow" | "RemoveBorrow";
  borrow: Borrow;
};

export type PathData = {
  heap: Record<string, string>;
  pcs: string[],
  borrow_actions_start: BorrowAction[];
  borrow_actions_mid: BorrowAction[];
  borrows: {
    borrows: Borrow[]
  }
  repacks_middle: string[]
  repacks_start: string[]
};

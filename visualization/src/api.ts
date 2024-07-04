import { Assertion } from "./components/Assertions";

export type MirGraphNode = {
  id: string;
  block: number;
  stmts: string[];
  terminator: string;
};

export type MirGraphEdge = {
  source: string;
  target: string;
  label: string;
};

type MirGraph = {
  nodes: MirGraphNode[];
  edges: MirGraphEdge[];
};

const fetchJsonFile = async (filePath: string) => {
  const response = await fetch(filePath);
  return await response.json();
};

export async function getGraphData(func: string): Promise<MirGraph> {
  const graphFilePath = `data/${func}/mir.json`;
  return await fetchJsonFile(graphFilePath);
}

export async function getFunctions(): Promise<Record<string, string>> {
  return await fetchJsonFile("data/functions.json");
}

export const getPaths = async (functionName: string) => {
  try {
    const paths: number[][] = await fetchJsonFile(
      `data/${functionName}/paths.json`
    );
    return paths;
  } catch (error) {
    console.error(error);
    return [];
  }
};

export const getAssertions = async (functionName: string) => {
  try {
    const assertions: Assertion[] = await fetchJsonFile(
      `data/${functionName}/assertions.json`
    );
    return assertions;
  } catch (error) {
    console.error(error);
    return [];
  }
};

export async function getPathData(
  functionName: string,
  path: number[],
  stmt: number
) {
  const endpoint = `data/${functionName}/path_${path.map((block) => `bb${block}`).join("_")}_stmt_${stmt}.json`;
  return await fetchJsonFile(endpoint);
}

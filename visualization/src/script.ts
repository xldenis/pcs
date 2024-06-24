import * as d3 from "d3";
import * as dagre from "@dagrejs/dagre";
import * as Viz from "@viz-js/viz";

type CurrentPoint = {
  block: number;
  stmt: number;
};

let currentPoint: CurrentPoint = {
  block: 0,
  stmt: 0,
};
let selectedFunction = "";

async function fetchJsonFile(filePath: string) {
  const response = await fetch(filePath);
  return await response.json();
}

async function fetchDotFile(filePath: string) {
  const response = await fetch(filePath);
  return await response.text();
}

async function populateFunctionDropdown() {
  const functions: string[] = await fetchJsonFile("data/functions.json");
  const select = document.getElementById("function-select");
  if (!select) {
    console.error("Function select element not found");
    return;
  }
  functions.forEach((func) => {
    const option = document.createElement("option");
    option.value = func;
    option.textContent = func;
    select.appendChild(option);
  });

  select.addEventListener("change", (event: any) => {
    selectedFunction = event.target.value;
    renderGraph();
  });

  // Set the initial selected function and render the graph
  if (functions.length > 0) {
    selectedFunction = functions[0];
    renderGraph();
  }
}

async function renderGraph() {
  if (!selectedFunction) return;

  const graphFilePath = `data/${selectedFunction}/mir.json`;
  const graph: {
    nodes: { id: string; label: string }[];
    edges: { source: string; target: string; label: string }[];
  } = await fetchJsonFile(graphFilePath);

  const g = new dagre.graphlib.Graph()
    .setGraph({})
    .setDefaultEdgeLabel(() => ({}));

  graph.nodes.forEach((node) => {
    g.setNode(node.id, { label: node.label });
  });

  graph.edges.forEach((edge) => {
    g.setEdge(edge.source, edge.target, { label: edge.label });
  });

  dagre.layout(g);

  const graphElement = document.getElementById("graph");
  if (!graphElement) {
    console.error("Graph element not found");
    return;
  }
  graphElement.innerHTML = "";
  const svg = d3.select("#graph").append("svg");

  const node = svg
    .append("g")
    .selectAll("g")
    .data(g.nodes())
    .enter()
    .append("g")
    .attr("class", "node")
    .attr("transform", (d: string) => {
      const node = g.node(d);
      return `translate(${node.x - node.width / 2},${node.y - node.height / 2})`;
    });

  node
    .append("foreignObject")
    .attr("width", 200)
    .attr("height", 600)
    .attr("class", "foreign-object")
    .html((d: string) => g.node(d).label);

  // Compute the actual height and width of each HTML table and update the corresponding node in dagre
  document.querySelectorAll("table[data-bb]").forEach((table) => {
    const bb = table.getAttribute("data-bb");
    if (bb === null) {
      return;
    }
    const rect = table.getBoundingClientRect();
    const width = rect.width;
    const height = rect.height;

    // Update the node in dagre
    const node = g.node(bb);
    node.width = width;
    node.height = height;
  });

  // Recompute the layout with updated node dimensions
  dagre.layout(g);

  // Calculate width and height of the complete graph
  const graphWidth =
    Math.max(...g.nodes().map((d) => g.node(d).x + g.node(d).width / 2)) + 20;
  const graphHeight =
    Math.max(...g.nodes().map((d) => g.node(d).y + g.node(d).height / 2)) + 20;

  // Update SVG dimensions based on calculated values
  svg.attr("width", graphWidth).attr("height", graphHeight);

  // Transform the nodes to their new positions
  node.attr("transform", (d: any) => {
    const node = g.node(d);
    return `translate(${node.x - node.width / 2},${node.y - node.height / 2})`;
  });

  // Draw edges
  const link = svg
    .append("g")
    .selectAll("path")
    .data(g.edges())
    .enter()
    .append("path")
    .attr("class", "link")
    .attr("id", (d: any, i: number) => `link${i}`)
    .attr("d", (d: any) => {
      const source = g.node(d.v);
      const target = g.node(d.w);
      const sourceX = source.x;
      const sourceY = source.y + source.height / 2;
      const targetX = target.x;
      const targetY = target.y - target.height / 2;
      return `M${sourceX},${sourceY}L${targetX},${targetY}`;
    });

  const edgeLabels = svg
    .append("g")
    .selectAll(".edge-label")
    .data(g.edges())
    .enter()
    .append("text")
    .attr("class", "link-label")
    .attr("dy", -5)
    .append("textPath")
    .attr("xlink:href", (d: any, i: number) => `#link${i}`)
    .attr("startOffset", "50%")
    .text((d: any) => g.edge(d).label);

  svg.on("click", async function (event: any) {
    const row = event.target.closest("tr");
    if (row) {
      selectRow(row);
    }
  });

  // Initial highlight of the first row
  const initialRow = document.querySelector(
    "tr[data-bb='0'][data-statement='0']"
  );
  if (initialRow) {
    selectRow(initialRow);
  }
}

document.addEventListener("keydown", function (event) {
  if (
    event.key === "ArrowUp" ||
    event.key === "ArrowDown" ||
    event.key === "k" ||
    event.key === "j"
  ) {
    event.preventDefault();
    if (currentPoint) {
      let newStmt;
      if (event.key === "ArrowUp" || event.key === "k") {
        newStmt = currentPoint.stmt - 1;
      } else {
        newStmt = currentPoint.stmt + 1;
      }
      const row = document.querySelector(
        `tr[data-bb='${currentPoint.block}'][data-statement='${newStmt}']`
      );
      if (row) {
        selectRow(row);
      }
    }
  }
});

// Highlights a row and renders the corresponding DOT graph
async function selectRow(row: Element) {
  const statement = row.getAttribute("data-statement");
  const bb = row.getAttribute("data-bb");
  currentPoint.stmt = parseInt(statement);
  currentPoint.block = parseInt(bb);
  console.log("Statement:", statement, "BB:", bb);

  d3.selectAll(".highlight").classed("highlight", false);

  d3.select(row).classed("highlight", true);

  const dotFilePath = `data/${selectedFunction}/block_${bb}_stmt_${statement}.dot`;

  try {
    const dotData = await fetchDotFile(dotFilePath);
    const dotGraph = document.getElementById("dot-graph");
    if (!dotGraph) {
      console.error("Dot graph element not found");
      return;
    }
    Viz.instance().then(function (viz) {
      dotGraph.innerHTML = "";
      dotGraph.appendChild(viz.renderSVGElement(dotData));
    });
  } catch (error) {
    console.error("Error fetching or rendering DOT file:", error);
  }
}

window.onload = populateFunctionDropdown;

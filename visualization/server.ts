import { serve } from "https://deno.land/std@0.140.0/http/server.ts";

const handler = async (request: Request): Promise<Response> => {
  const url = new URL(request.url);
  const filePath = url.pathname === "/" ? "/index.html" : url.pathname;
  
  try {
    const file = await Deno.readFile(`.${filePath}`);
    const headers = new Headers();
    headers.set("Content-Type", getContentType(filePath));
    headers.set("Cache-Control", "no-store, no-cache, must-revalidate");
    headers.set("Pragma", "no-cache");
    headers.set("Expires", "0");
    return new Response(file, { headers });
  } catch {
    return new Response("404 Not Found", { status: 404 });
  }
};

function getContentType(filePath: string): string {
  const extension = filePath.split(".").pop()?.toLowerCase();
  switch (extension) {
    case "html": return "text/html";
    case "js": return "application/javascript";
    case "css": return "text/css";
    case "json": return "application/json";
    default: return "application/octet-stream";
  }
}

console.log("Server running on http://localhost:8000");
await serve(handler, { port: 8000 });

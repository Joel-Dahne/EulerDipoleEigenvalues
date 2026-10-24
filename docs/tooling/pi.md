# Pi tooling

Each Pi session starts its own `lean-lsp-mcp` server over stdio using
[`.pi/mcp.json`](../../.pi/mcp.json). Start Pi from the repository root so
`--lean-project-path .` resolves correctly. No separate server command is needed.

Trust the project MCP configuration. After changing it, run `/reload` in
existing Pi sessions. Check the connection from the repository root with:

```sh
pi mcp list --json
```

The `lean-lsp` entry should report `connected` and the `lean-lsp-mcp` command.
Other clients use [`.mcp.json`](../../.mcp.json) with the same stdio command.

import MathEngine
/-- Native host: newline-delimited JSON-RPC over stdio (matches `stdioTransport` in engine-host).
The session store lives in this loop; the engine itself is a pure function. -/
partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) (st : MathEngine.Store) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let line := line.trimAsciiEnd.copy
  if line.isEmpty then loop stdin stdout st else
  let (st, out) := MathEngine.handleS st line
  stdout.putStrLn out
  stdout.flush
  loop stdin stdout st

def main : IO Unit := do loop (← IO.getStdin) (← IO.getStdout) []

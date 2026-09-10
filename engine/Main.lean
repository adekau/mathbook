import MathEngine
/-- Native host: newline-delimited JSON-RPC over stdio (matches `stdioTransport` in engine-host). -/
partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let line := line.trimAsciiEnd.copy
  if !line.isEmpty then
    stdout.putStrLn (MathEngine.handle line)
    stdout.flush
  loop stdin stdout

def main : IO Unit := do loop (← IO.getStdin) (← IO.getStdout)

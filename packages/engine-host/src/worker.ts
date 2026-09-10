/// <reference lib="webworker" />
import { serve } from "@mathbook/protocol";
import { Engine } from "@mathbook/reference-ts";
import { workerSelfTransport } from "./transports.js";

// Entry point for the in-browser engine. Bundle this file (scripts/bundle.mjs) and
// `new Worker("engine.worker.js")` from the page.
serve(workerSelfTransport(self as unknown as DedicatedWorkerGlobalScope), new Engine());

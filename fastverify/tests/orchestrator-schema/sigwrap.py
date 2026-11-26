"""tests/orchestrator-schema/sigwrap.py MODE FV [fastverify args...] - runs FV/lib/fastverify.py in-process with an injected event:
  final-after   SIGTERM right after the final atomic replace of result.json (os.replace in save() with run.final set)
  final-before  SIGTERM right before that replace
  no-autotune   autotune_preset raises (the optional tuner unavailable)
(a test driver only; the run itself is the package's own code path)"""
import os, runpy, signal, sys
mode, fv, *argv = sys.argv[1:]
mod = os.path.join(fv, "lib", "fastverify.py")
if mode in ("final-after", "final-before"):
    when = "c_return" if mode == "final-after" else "c_call"

    def trace(frame, event, fn):
        if event == when and fn is os.replace and frame.f_code.co_name == "save":
            run = frame.f_locals.get("self")
            if run is not None and getattr(run, "final", False):
                sys.setprofile(None)
                os.kill(os.getpid(), signal.SIGTERM)
    sys.argv = [mod] + argv
    sys.setprofile(trace)
    runpy.run_path(mod, run_name="__main__")
elif mode == "no-autotune":
    g = runpy.run_path(mod, run_name="fv_noautotune")

    def broken(a, pre):
        raise RuntimeError("host probe unavailable")
    g["main"].__globals__["autotune_preset"] = broken
    sys.argv = [mod] + argv
    g["reset_inherited_signals"]()
    sys.exit(g["main"]())

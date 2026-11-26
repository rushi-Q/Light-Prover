#!/usr/bin/python3 -I
"""test-dispatch-error.py: fvserve's dispatcher must survive an exception from take_batch() WITH THE REAL log()
(log() takes self.lock, the condition's non-reentrant lock -> logging inside 'with self.cv'
self-deadlocked). Injects one exception, then checks: dispatcher alive, lock free, 'dispatch-error' logged, and the
attempt is dispatched on the next round. Also re-runs the linger+cancel case with the real log().
env FVSERVE_PY = the fvserve.py to test. Exit 0 = pass."""
import importlib.util, io, os, sys, threading, time, types

FV = os.environ.get("FVSERVE_PY") or os.path.join(os.path.dirname(os.path.realpath(__file__)), "..", "..", "..", "..", "..",
                                                   "fastverify", "tools", "fvserve", "fvserve.py")


def service(m, fair, linger):
    svc = object.__new__(m.Service)
    svc.lock = threading.Lock(); svc.cv = threading.Condition(svc.lock)
    svc.pending = m.collections.deque(); svc.inflight = 0; svc.served = {}; svc.nserved = 0; svc.started = {}
    svc.nlaunch = 0; svc.nbatch = 0; svc.nitem = 0; svc.stop_flag = False; svc.stats = m.collections.Counter()
    svc.logf = io.StringIO(); svc.t0 = time.time()                      # the REAL log() of the class is used
    svc.a = types.SimpleNamespace(linger=linger, max_inflight=4, max_batch=8, slow_after=0, max_slow=4, fair=fair,
                                  isolate_suspects=True)
    return svc


def case(fair, inject):
    spec = importlib.util.spec_from_file_location("fvserve_t", FV); m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    svc = service(m, fair, linger=0.0 if inject else 0.15)
    ran = []
    svc.run_batch = lambda batch: ran.append([it.theorem for it in batch])
    if inject:
        real, calls = svc.take_batch, []
        def flaky():
            calls.append(1)
            if len(calls) == 1:
                raise RuntimeError("injected take_batch failure")
            return real()
        svc.take_batch = flaky
    caught = []
    def disp():
        try:
            svc.dispatcher()
        except BaseException as e:  # noqa: BLE001
            caught.append(repr(e))
    t = threading.Thread(target=disp, daemon=True); t.start(); time.sleep(0.02)
    if inject:
        svc.submit("pset", "thm1", "by rfl", "c:a1")
        time.sleep(1.6)                          # the error round waits 1 s, then the attempt is taken again
    else:
        it = svc.submit("pset", "thm1", "by rfl", "c:a1"); time.sleep(0.03); svc.cancel(it)
        time.sleep(0.4)
        svc.submit("pset", "thm2", "by rfl", "c:a1"); time.sleep(0.5)
    free = svc.lock.acquire(timeout=2)
    if free:
        svc.lock.release()
    alive = t.is_alive()
    svc.stop_flag = True
    if svc.lock.acquire(timeout=2):            # a deadlocked dispatcher holds the lock forever: do not hang the test
        svc.cv.notify_all()
        svc.lock.release()
    logged = "dispatch-error" in svc.logf.getvalue()
    ok = alive and free and not caught and ran and (logged or not inject)
    print(f"fair={fair!s:5} inject={inject!s:5} | alive={alive} lock_free={free} logged={logged} ran={ran} caught={caught} -> "
          f"{'PASS' if ok else 'FAIL'}")
    return ok


if __name__ == "__main__":
    res = [case(f, i) for i in (True, False) for f in (False, True)]
    sys.exit(0 if all(res) else 1)

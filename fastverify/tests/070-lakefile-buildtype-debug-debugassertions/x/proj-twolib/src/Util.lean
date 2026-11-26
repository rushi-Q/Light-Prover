-- Util belongs to lean_lib A (first, default target, no options) AND lean_lib B (autoImplicit = false).
-- Lake's Package.findModule? searches libs in REVERSE order (Lake/Config/Module.lean:59 findSomeRev?) -> import resolves to B.
def idf (x : α) : α := x

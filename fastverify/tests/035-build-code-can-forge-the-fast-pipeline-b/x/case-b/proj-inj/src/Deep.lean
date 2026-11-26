import Inject
-- needs more than the default maxRecDepth (512): the official build fails here
theorem deep : (List.replicate 3000 1).sum = 3000 := by decide

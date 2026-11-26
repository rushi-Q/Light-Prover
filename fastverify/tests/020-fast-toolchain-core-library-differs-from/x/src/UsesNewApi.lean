import Lean
-- a helper that is NOT part of any exported theorem's closure uses a fast-only core declaration
#check @Lean.registerScopedEnvExtensionWithImporter
theorem main_thm : 2 + 2 = 4 := rfl

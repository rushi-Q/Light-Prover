import HB
-- pure code only: three interpreted tactic calls that each read the imported closed term `table`
set_option maxHeartbeats 800 in
theorem t : 2 + 2 = 4 := by
  touch_table
  touch_table
  use_table

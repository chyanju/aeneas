module
public import Aeneas
public import MatchNegativeLiterals.MatchNegativeLiterals
public section

open Aeneas Aeneas.Std Result

/-! Matches with negative literal patterns: every match takes the branch of a
pattern for the value of this pattern exactly. -/

namespace match_negative_literals

/-! The patterns of the generated code are the scalars of the Rust patterns. -/

theorem i8_neg_1 : (255#iscalar : Std.I8) = (-1)#i8 := by decide
theorem i8_neg_2 : (254#iscalar : Std.I8) = (-2)#i8 := by decide
theorem i8_neg_127 : (129#iscalar : Std.I8) = (-127)#i8 := by decide
theorem i8_min : (128#iscalar : Std.I8) = (-128)#i8 := by decide
theorem i8_max : (127#iscalar : Std.I8) = 127#i8 := by decide
theorem i8_0 : (0#iscalar : Std.I8) = 0#i8 := by decide
theorem i8_1 : (1#iscalar : Std.I8) = 1#i8 := by decide
theorem i16_neg_1 : (65535#iscalar : Std.I16) = (-1)#i16 := by decide
theorem i16_min : (32768#iscalar : Std.I16) = (-32768)#i16 := by decide
theorem i16_1 : (1#iscalar : Std.I16) = 1#i16 := by decide
theorem i32_neg_1 : (4294967295#iscalar : Std.I32) = (-1)#i32 := by decide
theorem i32_min : (2147483648#iscalar : Std.I32) = (-2147483648)#i32 := by decide
theorem i32_1 : (1#iscalar : Std.I32) = 1#i32 := by decide
theorem i64_neg_1 : (18446744073709551615#iscalar : Std.I64) = (-1)#i64 := by decide
theorem i64_min :
    (9223372036854775808#iscalar : Std.I64) = (-9223372036854775808)#i64 := by decide
theorem i64_1 : (1#iscalar : Std.I64) = 1#i64 := by decide
theorem i128_neg_1 :
    (340282366920938463463374607431768211455#iscalar : Std.I128) = (-1)#i128 := by decide
theorem i128_min :
    (170141183460469231731687303715884105728#iscalar : Std.I128) =
      (-170141183460469231731687303715884105728)#i128 := by decide
theorem i128_1 : (1#iscalar : Std.I128) = 1#i128 := by decide

/-! The matches. -/

theorem code_i8_eq (v : Std.I8) :
    code_i8 v = ok (if v = 1#i8 then 1#u8 else if v = (-1)#i8 then 0#u8 else 2#u8) := by
  rw [← i8_neg_1, ← i8_1]
  unfold code_i8
  split <;> simp_all

theorem bounds_i8_eq (v : Std.I8) :
    bounds_i8 v =
      ok (if v = (-128)#i8 then 1#u8 else if v = (-127)#i8 then 2#u8
        else if v = (-2)#i8 then 3#u8 else if v = 127#i8 then 4#u8
        else if v = 0#i8 then 5#u8 else 0#u8) := by
  rw [← i8_min, ← i8_neg_127, ← i8_neg_2, ← i8_max, ← i8_0]
  unfold bounds_i8
  split <;> simp_all

theorem negative_only_i8_eq (v : Std.I8) :
    negative_only_i8 v =
      ok (if v = (-1)#i8 then 1#u8 else if v = (-2)#i8 then 2#u8 else 0#u8) := by
  rw [← i8_neg_1, ← i8_neg_2]
  unfold negative_only_i8
  split <;> simp_all

theorem code_i16_eq (v : Std.I16) :
    code_i16 v =
      ok (if v = (-1)#i16 then 1#u8 else if v = (-32768)#i16 then 2#u8
        else if v = 1#i16 then 3#u8 else 0#u8) := by
  rw [← i16_neg_1, ← i16_min, ← i16_1]
  unfold code_i16
  split <;> simp_all

theorem code_i32_eq (v : Std.I32) :
    code_i32 v =
      ok (if v = (-1)#i32 then 1#u8 else if v = (-2147483648)#i32 then 2#u8
        else if v = 1#i32 then 3#u8 else 0#u8) := by
  rw [← i32_neg_1, ← i32_min, ← i32_1]
  unfold code_i32
  split <;> simp_all

theorem code_i64_eq (v : Std.I64) :
    code_i64 v =
      ok (if v = (-1)#i64 then 1#u8 else if v = (-9223372036854775808)#i64 then 2#u8
        else if v = 1#i64 then 3#u8 else 0#u8) := by
  rw [← i64_neg_1, ← i64_min, ← i64_1]
  unfold code_i64
  split <;> simp_all

theorem code_i128_eq (v : Std.I128) :
    code_i128 v =
      ok (if v = (-1)#i128 then 1#u8
        else if v = (-170141183460469231731687303715884105728)#i128 then 2#u8
        else if v = 1#i128 then 3#u8 else 0#u8) := by
  rw [← i128_neg_1, ← i128_min, ← i128_1]
  unfold code_i128
  split <;> simp_all

end match_negative_literals

module
public import Aeneas
public import VecMethods.VecMethods
public section

open Aeneas Aeneas.Std Result

/-! Proofs for the `Vec::is_empty` and `Vec::insert` examples. -/

namespace vec_methods

/-- A new vector is empty… -/
theorem new_is_empty_spec : new_is_empty ⦃ b => b = true ⦄ := by
  unfold new_is_empty
  step*

/-- …and is not empty after a `push`. -/
theorem pushed_is_empty_spec : pushed_is_empty ⦃ b => b = false ⦄ := by
  unfold pushed_is_empty
  step*

/-- `is_empty` guarding an index: its spec gives the bound needed to index the vector. -/
theorem first_or_spec (v : alloc.vec.Vec Std.U32) (d : Std.U32) :
    first_or v d ⦃ x => x = if v.length = 0 then d else v.val[0]! ⦄ := by
  unfold first_or
  step*
  grind

/-- The example of the documentation of `Vec::insert`: the second insertion, at the length,
    appends. -/
theorem insert_doc_spec (v : alloc.vec.Vec Char) (h : v.val = ['a', 'b', 'c']) :
    insert_doc v ⦃ v' => v'.val = ['a', 'd', 'b', 'c', 'e'] ⦄ := by
  unfold insert_doc
  step* <;> grind

/-- `insert` succeeds at every position up to the length of the vector… -/
theorem insert_at_spec (v : alloc.vec.Vec Std.U32) (index : Std.Usize) (x : Std.U32)
    (hi : index.val ≤ v.length) (hs : v.length < Std.Usize.max) :
    insert_at v index x ⦃ v' => v'.val = v.val.insertIdx index.val x ⦄ := by
  unfold insert_at
  step*

/-- …and fails beyond it, where Rust panics. -/
theorem insert_at_past_len (v : alloc.vec.Vec Std.U32) (index : Std.Usize) (x : Std.U32)
    (hi : v.length < index.val) : insert_at v index x = fail .arrayOutOfBounds := by
  unfold insert_at
  exact alloc.vec.Vec.insert_eq_fail v index x hi

/-- An insertion at the length of the vector appends. -/
theorem insert_at_len_spec (v : alloc.vec.Vec Std.U32) (x : Std.U32)
    (hs : v.length < Std.Usize.max) :
    insert_at_len v x ⦃ v' => v'.val = v.val ++ [x] ⦄ := by
  unfold insert_at_len
  step*
  simp [*]

end vec_methods

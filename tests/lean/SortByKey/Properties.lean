module
public import Aeneas
public import SortByKey.SortByKey
public section

open Aeneas Aeneas.Std Result alloc.slice.Slice

/-! Proofs for the `<[T]>::sort_by_key` examples. The model is an opaque function of the
elements: a sort that returns gives a permutation of the elements (`sort_by_key_perm`) and, when
the key function computes the keys without changing its state and the `Ord` of the keys is a
total order on them, the stable sort by the keys (`sort_by_key_isStableSortByKey`, with
`sort_by_key_eq_of_isStableSortByKey` for a list known to be one). -/

namespace sort_by_key

/-- The absolute values of the elements of the example of the documentation. -/
def absKey (x : Std.I32) : Std.I32 :=
  if x = (-5)#i32 then 5#i32 else if x = (-3)#i32 then 3#i32 else x

/-- The example of the documentation: `[4, -5, 1, -3, 2]` sorted by the absolute values. -/
theorem sort_abs_doc {s s' : Slice Std.I32}
    (hs : s.val = [4#i32, (-5)#i32, 1#i32, (-3)#i32, 2#i32]) (h : sort_abs s = ok s') :
    s'.val = [1#i32, 2#i32, (-3)#i32, 4#i32, (-5)#i32] := by
  unfold sort_abs at h
  refine sort_by_key_eq_of_isStableSortByKey h (k := absKey) ?_
    (core.cmp.OrdI32.ordComputes _) ?_
  · rw [hs]
    unfold KeyedBy
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [sort_abs.closure.Insts.CoreOpsFunctionFnMutTupleShared0I32I32.call_mut]
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> step* <;> simp [absKey] <;> scalar_tac
  · rw [hs]
    unfold IsStableSortByKey
    decide

/-- Whatever the elements, a sort that returns gives a permutation of them. -/
theorem sort_abs_perm {s s' : Slice Std.I32} (h : sort_abs s = ok s') : s'.val.Perm s.val := by
  unfold sort_abs at h
  exact sort_by_key_perm h

/-- The key function of `sort_by_first` computes the first components. -/
theorem sort_by_first_keyed (l : List (Std.U32 × Std.U32)) :
    KeyedBy sort_by_first.closure.Insts.CoreOpsFunctionFnMutTupleShared0PairU32U32U32 () l
      (fun p => p.1) := by
  unfold KeyedBy
  intro ⟨a1, a2⟩ _
  simp [sort_by_first.closure.Insts.CoreOpsFunctionFnMutTupleShared0PairU32U32U32.call_mut]

/-- The pairs sorted by their first components, the pairs of equal first components in their
    initial order. -/
theorem sort_by_first_spec {s s' : Slice (Std.U32 × Std.U32)} (h : sort_by_first s = ok s') :
    IsStableSortByKey s.val s'.val (fun p => p.1) (fun x y => compare x.val y.val) := by
  unfold sort_by_first at h
  exact sort_by_key_isStableSortByKey h (sort_by_first_keyed _) (core.cmp.OrdU32.ordComputes _)

/-- The example of the Rust test `sort_by_key_stable`. -/
theorem sort_by_first_example {s s' : Slice (Std.U32 × Std.U32)}
    (hs : s.val = [(2#u32, 0#u32), (1#u32, 1#u32), (2#u32, 2#u32), (1#u32, 3#u32)])
    (h : sort_by_first s = ok s') :
    s'.val = [(1#u32, 1#u32), (1#u32, 3#u32), (2#u32, 0#u32), (2#u32, 2#u32)] := by
  unfold sort_by_first at h
  refine sort_by_key_eq_of_isStableSortByKey h (sort_by_first_keyed _)
    (core.cmp.OrdU32.ordComputes _) ?_
  rw [hs]
  unfold IsStableSortByKey
  decide

/-- The residue of `x` modulo `m`, as the closure computes it. -/
def residue (m x : Std.U32) : Std.U32 := ⟨x.bv % m.bv⟩

theorem residue_val (m x : Std.U32) : (residue m x).val = x.val % m.val := by
  show (x.bv % m.bv).toNat = _
  rw [BitVec.toNat_umod, UScalar.bv_toNat, UScalar.bv_toNat]

/-- With a nonzero modulus, the key function of `sort_by_residue` computes the residues. -/
theorem sort_by_residue_keyed (l : List Std.U32) {m : Std.U32} (hm : m.val ≠ 0) :
    KeyedBy sort_by_residue.closure.Insts.CoreOpsFunctionFnMutTupleShared1U32U32 m l
      (residue m) := by
  unfold KeyedBy
  intro a _
  simp only [sort_by_residue.closure.Insts.CoreOpsFunctionFnMutTupleShared1U32U32.call_mut]
  step*
  apply UScalar.eq_of_val_eq
  rw [i_post, residue_val]

/-- With a nonzero modulus, the elements sorted by their residues, the elements of equal residues
    in their initial order. -/
theorem sort_by_residue_spec {s s' : Slice Std.U32} {m : Std.U32} (hm : m.val ≠ 0)
    (h : sort_by_residue s m = ok s') :
    IsStableSortByKey s.val s'.val (residue m) (fun x y => compare x.val y.val) := by
  unfold sort_by_residue at h
  exact sort_by_key_isStableSortByKey h (sort_by_residue_keyed _ hm)
    (core.cmp.OrdU32.ordComputes _)

end sort_by_key

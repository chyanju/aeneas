/- `alloc::slice` -/
module
public import Aeneas.Std.Alloc.Vec
public import Aeneas.Std.Core.Cmp
public import Aeneas.Std.Core.Ops
public import Aeneas.Std.Scalar.EqOrd

public section

namespace Aeneas.Std

open Result WP ScalarElab

@[expose, rust_fun "alloc::slice::{[@T]}::to_vec"]
def alloc.slice.Slice.to_vec
  {T : Type _} (cloneInst : core.clone.Clone T) (s : Slice T) : Result (alloc.vec.Vec T) := do
  let s ← Slice.clone cloneInst.clone s
  ok {slice := s}

@[step]
theorem alloc.slice.Slice.to_vec_spec {T : Type _} (cloneInst : core.clone.Clone T) (s : Slice T)
  (h : ∀ x ∈ s.val, cloneInst.clone x = ok x) :
  alloc.slice.Slice.to_vec cloneInst s ⦃ s' => s = s'.slice ⦄ := by
  simp only [to_vec]
  apply Std.WP.spec_bind (Slice.clone_spec h)
  intro s' hs
  simpa using hs

@[expose, rust_fun "alloc::slice::{[@T]}::into_vec" -canFail -lift (keepParams := [true, false])]
def alloc.slice.Slice.into_vec
  {T : Type _} (s: Slice T) : (alloc.vec.Vec T) := {slice := s}

/-! ## `<[T]>::sort_by_key`

The documentation (<https://doc.rust-lang.org/std/primitive.slice.html#method.sort_by_key>):
"Sorts the slice in ascending order with a key extraction function, preserving initial order of
equal elements"; "This sort is stable (i.e., does not reorder equal elements)"; if the `Ord` of
the keys is not a total order, "the function may panic; even if the function exits normally, the
resulting order of elements in the slice is unspecified"; and if it panics, "all original elements
will remain in the slice". The source calls `stable_sort(self, |a, b| f(a).lt(&f(b)))`.

The model is an opaque function of the elements, the key function and the `Ord` instance into
the permutations of the elements, or a failure. A permutation that it returns is, when the key
function computes the keys without changing its state and the `Ord` instance a total order on
the keys (`KeyedBy`, `OrdComputes`), in ascending order of the keys, with the elements of equal
keys in their initial order (`IsStableSortByKey`). There is only one such permutation, the stable
sort `stableSortByKey` (`IsStableSortByKey.eq_stableSortByKey`). -/

namespace alloc.slice.Slice

/-- The key function `f` computes `k` on the elements of `l`: called on an element `a` of `l`, it
    returns `k a` and leaves its state unchanged. -/
@[expose] def KeyedBy {T K F : Type _} (inst : core.ops.function.FnMut F T K) (f : F)
    (l : List T) (k : T → K) : Prop :=
  ∀ a ∈ l, inst.call_mut f a ⦃ y f' => y = k a ∧ f' = f ⦄

/-- `c` is a total order on `ks` in the sense of `Ord` (distinct values may be equal): `c y x` is
    `c x y` swapped, and "`c x y` is not `.gt`" is transitive. -/
@[expose] def TotalOn {K : Type _} (ks : List K) (c : K → K → Ordering) : Prop :=
  (∀ x ∈ ks, ∀ y ∈ ks, c y x = (c x y).swap) ∧
    ∀ x ∈ ks, ∀ y ∈ ks, ∀ z ∈ ks, c x y ≠ .gt → c y z ≠ .gt → c x z ≠ .gt

/-- On `ks`, the `Ord` instance computes the total order `c`: `cmp` returns `c`, and `lt` whether
    `c` is `.lt`. -/
@[expose] def OrdComputes {K : Type _} (inst : core.cmp.Ord K) (ks : List K)
    (c : K → K → Ordering) : Prop :=
  (∀ x ∈ ks, ∀ y ∈ ks, inst.cmp x y ⦃ o => o = c x y ⦄) ∧
    (∀ x ∈ ks, ∀ y ∈ ks,
      inst.partialOrdInst.lt x y ⦃ b => b = decide (c x y = .lt) ⦄) ∧
    TotalOn ks c

/-- `l'` is the elements of `l` in ascending order of their keys `k` under `c`, the elements of
    equal keys in their order in `l`. -/
@[expose] def IsStableSortByKey {T K : Type _} (l l' : List T) (k : T → K)
    (c : K → K → Ordering) : Prop :=
  l'.Perm l ∧ l'.Pairwise (fun a b => c (k a) (k b) ≠ .gt) ∧
    ∀ e ∈ l, l'.filter (fun a => decide (c (k a) (k e) = .eq)) =
      l.filter (fun a => decide (c (k a) (k e) = .eq))

/-- The stable sort of `l` by the keys `k` under `c`. -/
@[expose] def stableSortByKey {T K : Type _} (l : List T) (k : T → K) (c : K → K → Ordering) :
    List T :=
  l.mergeSort fun a b => (c (k a) (k b)).isLE

/-- The result of `<[T]>::sort_by_key` on the elements `l`, the key function `f` and the `Ord`
    instance of the keys: a permutation of `l`, which is the stable sort by the keys when `f`
    computes them without changing its state and the instance computes a total order on them. -/
opaque sortByKeyResult {T K F : Type _} (inst : core.ops.function.FnMut F T K)
    (ordInst : core.cmp.Ord K) (l : List T) (f : F) :
    Result {l' : List T // l'.Perm l ∧ ∀ k c, KeyedBy inst f l k →
      OrdComputes ordInst (l.map k) c → IsStableSortByKey l l' k c}

end alloc.slice.Slice

/-- Model of `<[T]>::sort_by_key`
    (<https://doc.rust-lang.org/std/primitive.slice.html#method.sort_by_key>): a permutation of
    the elements, or a failure; when the key function computes the keys without changing its state
    and the `Ord` of the keys is a total order on them, the stable sort by the keys
    (`sort_by_key_perm`, `sort_by_key_eq`). -/
@[expose, rust_fun "alloc::slice::{[@T]}::sort_by_key"]
def alloc.slice.Slice.sort_by_key {T K F : Type _} (inst : core.ops.function.FnMut F T K)
    (ordInst : core.cmp.Ord K) (s : Slice T) (f : F) : Result (Slice T) := do
  let r ← alloc.slice.Slice.sortByKeyResult inst ordInst s.val f
  ok (Slice.from r.val (by rw [r.property.1.length_eq]; exact s.property))

namespace alloc.slice.Slice

theorem TotalOn.mono {K : Type _} {ks ks' : List K} {c : K → K → Ordering} (hc : TotalOn ks c)
    (h : ∀ x ∈ ks', x ∈ ks) : TotalOn ks' c :=
  ⟨fun x hx y hy => hc.1 x (h x hx) y (h y hy),
    fun x hx y hy z hz => hc.2 x (h x hx) y (h y hy) z (h z hz)⟩

theorem TotalOn.refl {K : Type _} {ks : List K} {c : K → K → Ordering} (hc : TotalOn ks c)
    {x : K} (hx : x ∈ ks) : c x x = .eq := by
  have h := hc.1 x hx x hx
  cases hxx : c x x <;> rw [hxx] at h <;> simp [Ordering.swap] at h ⊢

theorem TotalOn.not_gt_swap {K : Type _} {ks : List K} {c : K → K → Ordering}
    (hc : TotalOn ks c) {x y : K} (hx : x ∈ ks) (hy : y ∈ ks) (h : c x y = .gt) :
    c y x ≠ .gt := by
  rw [hc.1 x hx y hy, h]
  simp [Ordering.swap]

theorem TotalOn.eq_of_not_gt {K : Type _} {ks : List K} {c : K → K → Ordering}
    (hc : TotalOn ks c) {x y : K} (hx : x ∈ ks) (hy : y ∈ ks) (h1 : c x y ≠ .gt)
    (h2 : c y x ≠ .gt) : c x y = .eq := by
  rw [hc.1 x hx y hy] at h2
  cases hxy : c x y <;> rw [hxy] at h1 h2 <;> simp [Ordering.swap] at h1 h2 ⊢

theorem TotalOn.eq_trans {K : Type _} {ks : List K} {c : K → K → Ordering}
    (hc : TotalOn ks c) {x y z : K} (hx : x ∈ ks) (hy : y ∈ ks) (hz : z ∈ ks)
    (h1 : c x y = .eq) (h2 : c y z = .eq) : c x z = .eq := by
  have hyx : c y x = .eq := by rw [hc.1 x hx y hy, h1]; rfl
  have hzy : c z y = .eq := by rw [hc.1 y hy z hz, h2]; rfl
  refine hc.eq_of_not_gt hx hz ?_ ?_
  · exact hc.2 x hx y hy z hz (by rw [h1]; simp) (by rw [h2]; simp)
  · exact hc.2 z hz y hy x hx (by rw [hzy]; simp) (by rw [hyx]; simp)

/-- A stable sort is unique: two lists with the same elements, both in ascending order of the keys
    and with the same elements of each key in the same order, are equal. -/
theorem stable_sorted_unique {T K : Type _} {k : T → K} {c : K → K → Ordering} :
    ∀ {l₁ l₂ : List T}, TotalOn (l₁.map k) c → l₁.Perm l₂ →
      l₁.Pairwise (fun a b => c (k a) (k b) ≠ .gt) →
      l₂.Pairwise (fun a b => c (k a) (k b) ≠ .gt) →
      (∀ e ∈ l₁, l₁.filter (fun a => decide (c (k a) (k e) = .eq)) =
        l₂.filter (fun a => decide (c (k a) (k e) = .eq))) → l₁ = l₂
  | [], l₂, _, hp, _, _, _ => (List.perm_nil.mp hp.symm).symm
  | a :: r₁, [], _, hp, _, _, _ => absurd hp.length_eq (by simp)
  | a :: r₁, b :: r₂, hc, hp, hs₁, hs₂, hf => by
    have hkey : ∀ x ∈ a :: r₁, k x ∈ (a :: r₁).map k := fun x hx => List.mem_map_of_mem hx
    have ha : a ∈ a :: r₁ := List.mem_cons_self
    have hb : b ∈ a :: r₁ := hp.mem_iff.mpr List.mem_cons_self
    -- `a` and `b` have equal keys: each is not above the other
    have hab : c (k a) (k b) = .eq := by
      by_cases he : a = b
      · rw [he]; exact hc.refl (hkey b hb)
      · have hb' : b ∈ r₁ := by
          rcases List.mem_cons.mp hb with h | h
          · exact absurd h.symm he
          · exact h
        have ha' : a ∈ r₂ := by
          rcases List.mem_cons.mp (hp.mem_iff.mp ha) with h | h
          · exact absurd h he
          · exact h
        exact hc.eq_of_not_gt (hkey a ha) (hkey b hb) (List.rel_of_pairwise_cons hs₁ hb')
          (List.rel_of_pairwise_cons hs₂ ha')
    -- the elements of the key of `a` start with `a` in `l₁` and with `b` in `l₂`
    have hfa := hf a ha
    rw [List.filter_cons_of_pos (by simpa using hc.refl (hkey a ha)),
      List.filter_cons_of_pos (by
        have h := hc.1 (k a) (hkey a ha) (k b) (hkey b hb)
        rw [hab] at h
        simpa using h)] at hfa
    obtain ⟨rfl, -⟩ := List.cons.inj hfa
    refine congrArg (List.cons a) ?_
    refine stable_sorted_unique (hc.mono (fun x hx => List.mem_cons_of_mem _ hx))
      ((List.perm_cons a).mp hp)
      (List.pairwise_cons.mp hs₁).2 (List.pairwise_cons.mp hs₂).2 fun e he => ?_
    have h := hf e (List.mem_cons_of_mem a he)
    by_cases hae : c (k a) (k e) = .eq
    · rw [List.filter_cons_of_pos (by simpa using hae),
        List.filter_cons_of_pos (by simpa using hae)] at h
      exact (List.cons.inj h).2
    · rw [List.filter_cons_of_neg (by simpa using hae),
        List.filter_cons_of_neg (by simpa using hae)] at h
      exact h

/-- `stableSortByKey` is a stable sort by the keys: a permutation, in ascending order of the keys,
    with the elements of equal keys in their initial order. -/
theorem stableSortByKey_isStableSortByKey {T K : Type _} {l : List T} {k : T → K}
    {c : K → K → Ordering} (hc : TotalOn (l.map k) c) :
    IsStableSortByKey l (stableSortByKey l k c) k c := by
  have hk : ∀ x ∈ l, k x ∈ l.map k := fun x hx => List.mem_map_of_mem hx
  -- `mergeSort` on the elements of `l`, where the order is transitive and total
  let le : T → T → Bool := fun a b => (c (k a) (k b)).isLE
  let le' : {x // x ∈ l} → {x // x ∈ l} → Bool := fun a b => le a.1 b.1
  have htrans : ∀ a b d, le' a b → le' b d → le' a d := by
    intro a b d h1 h2
    simp only [le', le, Ordering.isLE_iff_ne_gt] at h1 h2 ⊢
    exact hc.2 _ (hk _ a.2) _ (hk _ b.2) _ (hk _ d.2) h1 h2
  have htotal : ∀ a b, le' a b || le' b a := by
    intro a b
    by_cases h : c (k a.1) (k b.1) = .gt
    · have h' := hc.not_gt_swap (hk _ a.2) (hk _ b.2) h
      simp only [le', le, Bool.or_eq_true, Ordering.isLE_iff_ne_gt]
      exact Or.inr h'
    · simp only [le', le, Bool.or_eq_true, Ordering.isLE_iff_ne_gt]
      exact Or.inl h
  have hmap : (l.attach.mergeSort le').map Subtype.val = l.mergeSort le := by
    rw [List.map_mergeSort (s := le) (fun a _ b _ => rfl), List.attach_map_subtype_val]
  have hperm : (l.mergeSort le).Perm l := List.mergeSort_perm l le
  refine ⟨hperm, ?_, fun e he => ?_⟩
  · -- in ascending order of the keys
    have hp := List.pairwise_mergeSort htrans htotal l.attach
    unfold stableSortByKey
    rw [← hmap, List.pairwise_map]
    refine hp.imp fun {a b} h => ?_
    simpa only [le', le, Ordering.isLE_iff_ne_gt] using h
  · -- the elements of the key of `e` in their initial order
    let p : T → Bool := fun a => decide (c (k a) (k e) = .eq)
    have hsub : (l.attach.filter fun a => p a.1).Sublist (l.attach.mergeSort le') := by
      refine List.sublist_mergeSort htrans htotal ?_ List.filter_sublist
      refine List.pairwise_of_forall_mem_list fun a ha b hb => ?_
      have ha' := (List.mem_filter.mp ha).2
      have hb' := (List.mem_filter.mp hb).2
      simp only [p, decide_eq_true_eq] at ha' hb'
      have hbe : c (k e) (k b.1) = .eq := by
        rw [hc.1 _ (hk _ b.2) _ (hk _ he), hb']
        rfl
      simp only [le', le, hc.eq_trans (hk _ a.2) (hk _ he) (hk _ b.2) ha' hbe]
      rfl
    have hfm : (l.attach.filter fun a => p a.1).map Subtype.val = l.filter p := by
      conv_rhs => rw [← List.attach_map_subtype_val l, List.filter_map]
      rfl
    have hsub' : (l.filter p).Sublist (l.mergeSort le) := by
      have h := hsub.map Subtype.val
      rwa [hmap, hfm] at h
    have hsub'' : (l.filter p).Sublist ((l.mergeSort le).filter p) := by
      have h := hsub'.filter p
      rwa [List.filter_filter, show (fun a => p a && p a) = p from funext fun a => by simp]
        at h
    exact (hsub''.eq_of_length (hperm.filter p).length_eq.symm).symm

/-- A stable sort of `l` by the keys is `stableSortByKey`. -/
theorem IsStableSortByKey.eq_stableSortByKey {T K : Type _} {l l' : List T} {k : T → K}
    {c : K → K → Ordering} (hc : TotalOn (l.map k) c) (h : IsStableSortByKey l l' k c) :
    l' = stableSortByKey l k c := by
  have hs := stableSortByKey_isStableSortByKey hc
  refine stable_sorted_unique (hc.mono fun x hx => ?_) (h.1.trans hs.1.symm) h.2.1 hs.2.1
    fun e he => ?_
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact List.mem_map_of_mem (h.1.mem_iff.mp ha)
  · have he' := h.1.mem_iff.mp he
    rw [h.2.2 e he', hs.2.2 e he']

/-- `<[T]>::sort_by_key` leaves a permutation of the elements. -/
theorem sort_by_key_perm {T K F : Type _} {inst : core.ops.function.FnMut F T K}
    {ordInst : core.cmp.Ord K} {s s' : Slice T} {f : F}
    (h : sort_by_key inst ordInst s f = ok s') : s'.val.Perm s.val := by
  unfold sort_by_key at h
  generalize sortByKeyResult inst ordInst s.val f = x at h
  cases x with
  | ret r =>
    simp only [bind_tc_eq, bind_ok, Result.ok.injEq] at h
    rw [← h, Slice.from_val]
    exact r.property.1
  | vis e k' => simp at h
  | div => simp at h

/-- When the key function computes the keys without changing its state and the `Ord` of the
    keys a total order on them, `<[T]>::sort_by_key` gives a stable sort of the elements by the
    keys, if it returns. -/
theorem sort_by_key_isStableSortByKey {T K F : Type _} {inst : core.ops.function.FnMut F T K}
    {ordInst : core.cmp.Ord K} {s s' : Slice T} {f : F} {k : T → K} {c : K → K → Ordering}
    (h : sort_by_key inst ordInst s f = ok s') (hk : KeyedBy inst f s.val k)
    (hc : OrdComputes ordInst (s.val.map k) c) : IsStableSortByKey s.val s'.val k c := by
  unfold sort_by_key at h
  generalize sortByKeyResult inst ordInst s.val f = x at h
  cases x with
  | ret r =>
    simp only [bind_tc_eq, bind_ok, Result.ok.injEq] at h
    rw [← h, Slice.from_val]
    exact r.property.2 k c hk hc
  | vis e k' => simp at h
  | div => simp at h

/-- When the key function computes the keys without changing its state and the `Ord` of the
    keys a total order on them, `<[T]>::sort_by_key` gives `stableSortByKey`, if it returns. -/
theorem sort_by_key_eq {T K F : Type _} {inst : core.ops.function.FnMut F T K}
    {ordInst : core.cmp.Ord K} {s s' : Slice T} {f : F} {k : T → K} {c : K → K → Ordering}
    (h : sort_by_key inst ordInst s f = ok s') (hk : KeyedBy inst f s.val k)
    (hc : OrdComputes ordInst (s.val.map k) c) : s'.val = stableSortByKey s.val k c :=
  (sort_by_key_isStableSortByKey h hk hc).eq_stableSortByKey hc.2.2

/-- When the key function computes the keys without changing its state and the `Ord` of the
    keys a total order on them, `<[T]>::sort_by_key` gives any stable sort `l` of the elements by
    the keys, if it returns. -/
theorem sort_by_key_eq_of_isStableSortByKey {T K F : Type _}
    {inst : core.ops.function.FnMut F T K} {ordInst : core.cmp.Ord K} {s s' : Slice T} {f : F}
    {k : T → K} {c : K → K → Ordering} {l : List T}
    (h : sort_by_key inst ordInst s f = ok s') (hk : KeyedBy inst f s.val k)
    (hc : OrdComputes ordInst (s.val.map k) c) (hl : IsStableSortByKey s.val l k c) :
    s'.val = l := by
  rw [sort_by_key_eq h hk hc, hl.eq_stableSortByKey hc.2.2]

end alloc.slice.Slice

uscalar
/-- The `Ord` of an unsigned scalar type computes the order of the values. -/
theorem core.cmp.Ord'S.ordComputes (ks : List «%S») :
    alloc.slice.Slice.OrdComputes core.cmp.Ord'S ks (fun x y => compare x.val y.val) := by
  refine ⟨fun x _ y _ => by simp, fun x _ y _ => ?_, fun x _ y _ => ?_,
    fun x _ y _ z _ h1 h2 => ?_⟩
  · simp [core.cmp.impls.PartialOrd'S.lt, Nat.compare_eq_lt]
  · exact (Nat.compare_swap x.val y.val).symm
  · exact Nat.compare_ne_gt.mpr (Nat.le_trans (Nat.compare_ne_gt.mp h1) (Nat.compare_ne_gt.mp h2))

iscalar
/-- The `Ord` of a signed scalar type computes the order of the values. -/
theorem core.cmp.Ord'S.ordComputes (ks : List «%S») :
    alloc.slice.Slice.OrdComputes core.cmp.Ord'S ks (fun x y => compare x.val y.val) := by
  refine ⟨fun x _ y _ => by simp, fun x _ y _ => ?_, fun x _ y _ => ?_,
    fun x _ y _ z _ h1 h2 => ?_⟩
  · simp [core.cmp.impls.PartialOrd'S.lt, Int.compare_eq_lt]
  · exact (Int.compare_swap x.val y.val).symm
  · exact Int.compare_ne_gt.mpr (Int.le_trans (Int.compare_ne_gt.mp h1) (Int.compare_ne_gt.mp h2))

end Aeneas.Std

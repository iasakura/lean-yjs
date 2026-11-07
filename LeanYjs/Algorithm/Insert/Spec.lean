import Mathlib.Tactic.WLOG
import Std.Tactic.Do

import LeanYjs.ListLemmas
import LeanYjs.Item
import LeanYjs.ItemSet
import LeanYjs.ClientId
import LeanYjs.Order.ItemOrder
import LeanYjs.Order.ItemSetInvariant
import LeanYjs.Order.Totality
import LeanYjs.Order.Transitivity
import LeanYjs.Order.Asymmetry
import LeanYjs.Order.NoCrossOrigin
import LeanYjs.Algorithm.Basic
import LeanYjs.Algorithm.Insert.Basic
import LeanYjs.Algorithm.Insert.Lemmas
import LeanYjs.Algorithm.Invariant.Basic
import LeanYjs.Algorithm.Invariant.YjsArray

/-!
# Insert preserves the array invariant

This file proves that `integrate` (and hence `YjsState.insert`) preserves
`YjsArrInvariant`: the new item is placed at the unique position that keeps the
array sorted under `YjsLt'`.

The proof follows the paper's loop-invariant argument for `findIntegratedIndex`:

* `IntegrateCtx` bundles the standing hypotheses (array invariant, the extended item
  set `u :: arr` is closed and satisfies `ItemSetInvariant`, clock maximality, and
  the positions `leftIdx`/`rightIdx` of `u.origin`/`u.rightOrigin`).
* `IntegrationInvariant arr u d i scanning done` is the loop invariant on the
  mathematical state: candidate destination `d`, scan position `i`, the
  `scanning` flag and whether the loop has exited by `break`.
* `IntegrationInvariant.init` and the six `IntegrationInvariant.step_*` lemmas
  establish the invariant at loop entry and preserve it along each branch of the
  loop body (one lemma per row of the paper's case table).
* `pending_propagation` collapses the pending region at loop exit, giving
  `SortedInsertPos`, the unique sorted insertion position.
* `findIntegratedIndex_spec` ties this to the executable loop with `mvcgen`;
  `ScanLoopInv` is the thin layer relating the loop's `⟨dest, scanning⟩` state and
  cursor to `IntegrationInvariant`.
* `YjsArrInvariant_insertIdxIfInBounds` and `YjsArrInvariant_integrate` conclude.
-/

variable {A : Type}
variable [DecidableEq A]

open Std.Do

/-! ## Validity of the new item -/

/-- Validity of an item relative to the order: its origin is below its right origin,
and every pointer origin-reachable from it lies outside the open interval
`(origin, rightOrigin)`. -/
structure IsItemValid (item : YjsItem A) where
  origin_lt_rightOrigin : YjsLt' (A := A) item.origin item.rightOrigin
  reachable_YjsLeq' : (∀ (x : YjsPtr A),
      OriginReachable (YjsPtr.itemPtr item) x →
      YjsLeq' (A := A) x item.origin ∨ YjsLeq' (A := A) item.rightOrigin x)

abbrev YjsItem.isValid : YjsItem A → Prop := IsItemValid

/-- `newItem`'s clock is strictly larger than that of every item of the same client
already in `arr`.  This is what `isClockSafe` decides (`isClockSafe_maximalId`). -/
def maximalId (newItem : YjsItem A) (arr : Array (YjsItem A)) :=
  ∀ (x : YjsItem A),
    ArrSet arr.toList (YjsPtr.itemPtr x) →
    x.id.clientId = newItem.id.clientId → x.id.clock < newItem.id.clock

/-! ## Small facts about the executable helpers -/

omit [DecidableEq A] in
theorem getElemExcept_eq_ok_iff {arr : Array (YjsItem A)} {i : ℕ} {x : YjsItem A} :
    getElemExcept arr i = Except.ok x ↔ ∃ h : i < arr.size, arr[i] = x := by
  unfold getElemExcept
  cases h : arr[i]? with
  | none =>
    simp only [Array.getElem?_eq_none_iff] at h
    constructor
    · intro h'; cases h'
    · rintro ⟨hi, _⟩; omega
  | some y =>
    rw [Array.getElem?_eq_some_iff] at h
    obtain ⟨hi, rfl⟩ := h
    constructor
    · intro h'; cases h'; exact ⟨hi, rfl⟩
    · rintro ⟨_, rfl⟩; rfl

lemma findPtrIdx_lt_size_getElem {arr : Array (YjsItem A)} {idx : ℤ} {p : YjsPtr A} :
  findPtrIdx p arr = Except.ok idx →
  0 ≤ idx ->
  (h : idx.toNat < arr.size) →
  arr[idx.toNat] = p := by
  intros hfind hlt hsize
  unfold findPtrIdx at hfind
  cases p with
  | first =>
    simp at hfind
    cases hfind
    omega
  | last =>
    simp at hfind
    cases hfind
    omega
  | itemPtr p =>
    simp at hfind
    generalize heq : Array.findIdx? (fun i => decide (i = p)) arr = idxOpt at hfind
    cases idxOpt <;> cases hfind
    rw [Array.findIdx?_eq_some_iff_getElem] at heq
    obtain ⟨ h, heq, _ ⟩ := heq
    simp at heq
    subst p
    simp

/-- Position bookkeeping for the offset list `[1 : n]` of the integration loop. -/
theorem List.range'_eq_append_cons {s n : ℕ} {pref suff : List ℕ} {cur : ℕ}
    (h : List.range' s n = pref ++ cur :: suff) :
    cur = s + pref.length ∧ pref.length + 1 + suff.length = n := by
  have hlen := congrArg List.length h
  simp at hlen
  have hcur : (List.range' s n)[pref.length]? = some cur := by
    rw [h, List.getElem?_append_right (le_refl _)]
    simp
  rw [List.getElem?_eq_getElem (by simp; omega), List.getElem_range'] at hcur
  simp at hcur
  omega

/-- The offset list of the integration loop `for offset in [1:n]`. -/
theorem Std.Range.toList_one (n : ℕ) : [1:n].toList = List.range' 1 (n - 1) := by
  simp only [Std.Range.toList]
  congr 1
  omega

/-! ## Id lists of index windows -/

/-- `l` lists exactly the ids of the elements of `arr` at the positions `lo ≤ k < hi`. -/
def IdsOfRange (arr : Array (YjsItem A)) (lo : ℤ) (hi : ℕ) (l : List YjsId) : Prop :=
  ∀ x, x ∈ l ↔ ∃ k : ℕ, lo ≤ k ∧ k < hi ∧ ∃ hk : k < arr.size, arr[k].id = x

namespace IdsOfRange

omit [DecidableEq A] in
theorem nil {arr : Array (YjsItem A)} {lo : ℤ} {hi : ℕ} (h : (hi : ℤ) ≤ lo) :
    IdsOfRange arr lo hi [] := fun x => by
  simp only [List.not_mem_nil, false_iff]
  rintro ⟨ k, h1, h2, _ ⟩
  omega

omit [DecidableEq A] in
theorem cons {arr : Array (YjsItem A)} {lo : ℤ} {i : ℕ} {l : List YjsId}
    (h : IdsOfRange arr lo i l) (hi : i < arr.size) (hlo : lo ≤ i) :
    IdsOfRange arr lo (i + 1) (arr[i].id :: l) := fun x => by
  rw [List.mem_cons, h x]
  constructor
  · rintro (rfl | ⟨ k, h1, h2, hk, rfl ⟩)
    · exact ⟨ i, hlo, by omega, hi, rfl ⟩
    · exact ⟨ k, h1, by omega, hk, rfl ⟩
  · rintro ⟨ k, h1, h2, hk, rfl ⟩
    rcases Nat.lt_or_ge k i with hk' | hk'
    · exact Or.inr ⟨ k, h1, hk', hk, rfl ⟩
    · obtain rfl : k = i := by omega
      exact Or.inl rfl

end IdsOfRange

/-! ## The integration context -/

/-- Standing hypotheses while integrating `u` into `arr`.  `leftIdx`/`rightIdx` are
the positions of `u.origin`/`u.rightOrigin` in `arr` (`-1` for `first`, `arr.size`
for `last`). -/
structure IntegrateCtx (arr : Array (YjsItem A)) (u : YjsItem A) (leftIdx rightIdx : ℤ) : Prop where
  arrInv : YjsArrInvariant arr.toList
  closed : IsClosedItemSet (ArrSet (u :: arr.toList))
  setInv : ItemSetInvariant (ArrSet (u :: arr.toList))
  maximal : maximalId u arr
  left : findPtrIdx u.origin arr = Except.ok leftIdx
  right : findPtrIdx u.rightOrigin arr = Except.ok rightIdx

namespace IntegrateCtx

variable {arr : Array (YjsItem A)} {u : YjsItem A} {leftIdx rightIdx : ℤ}
  (ctx : IntegrateCtx arr u leftIdx rightIdx)

omit [DecidableEq A] in
theorem u_mem : ArrSet (u :: arr.toList) u := by simp [ArrSet]

omit [DecidableEq A] in
theorem getElem_mem {i : ℕ} (hi : i < arr.size) : ArrSet (u :: arr.toList) arr[i] := by
  simp [ArrSet]

include ctx

theorem origin_mem : ArrSet (u :: arr.toList) u.origin :=
  origin_p_valid ctx.closed u u_mem

theorem rightOrigin_mem : ArrSet (u :: arr.toList) u.rightOrigin :=
  right_origin_p_valid ctx.closed u u_mem

theorem getElem_origin_mem {i : ℕ} (hi : i < arr.size) : ArrSet (u :: arr.toList) arr[i].origin :=
  origin_p_valid ctx.closed _ (getElem_mem hi)

theorem getElem_rightOrigin_mem {i : ℕ} (hi : i < arr.size) :
    ArrSet (u :: arr.toList) arr[i].rightOrigin :=
  right_origin_p_valid ctx.closed _ (getElem_mem hi)

theorem origin_lt_rightOrigin : YjsLt' (A := A) u.origin u.rightOrigin := by
  obtain ⟨ o, r, id, c ⟩ := u
  exact ctx.setInv.origin_not_leq o r c id u_mem

theorem left_ge : -1 ≤ leftIdx := findPtrIdx_ge_minus_1 _ ctx.left

theorem right_le : rightIdx ≤ arr.size := findPtrIdx_le_size _ ctx.right

theorem left_lt_right : leftIdx < rightIdx :=
  YjsLt'_findPtrIdx_lt _ _ _ _ _ ctx.arrInv (findPtrIdx_ArrSet ctx.left)
    (findPtrIdx_ArrSet ctx.right) ctx.origin_lt_rightOrigin ctx.left ctx.right

theorem left_lt_size : leftIdx < arr.size := lt_of_lt_of_le ctx.left_lt_right ctx.right_le

/-- Sortedness of `arr`, in index form. -/
theorem getElem_le {i j : ℕ} (hij : i ≤ j) (hj : j < arr.size) : YjsLeq' (A := A) arr[i] arr[j] :=
  getElem_leq_YjsLeq' arr i j ctx.arrInv hij hj

theorem findPtrIdx_getElem {i : ℕ} (hi : i < arr.size) : findPtrIdx arr[i] arr = Except.ok i :=
  _root_.findPtrIdx_getElem arr i ctx.arrInv hi

/-- Elements strictly right of `leftIdx` are above `u.origin`. -/
theorem origin_lt_getElem {i : ℕ} (hi : i < arr.size) (h : leftIdx < i) : YjsLt' (A := A) u.origin arr[i] :=
  findPtrIdx_lt_YjsLt' arr _ _ ctx.arrInv ctx.left (ctx.findPtrIdx_getElem hi) h

/-- Elements strictly left of `rightIdx` are below `u.rightOrigin`. -/
theorem getElem_lt_rightOrigin {i : ℕ} (hi : i < arr.size) (h : i < rightIdx) :
    YjsLt' (A := A) arr[i] u.rightOrigin :=
  findPtrIdx_lt_YjsLt' arr _ _ ctx.arrInv (ctx.findPtrIdx_getElem hi) ctx.right h

/-- `u` is fresh: its id differs from the id of every element of `arr`. -/
theorem id_ne {i : ℕ} (hi : i < arr.size) : arr[i].id ≠ u.id := by
  intro h
  have := ctx.maximal arr[i] (by simp [ArrSet]) (by rw [h])
  rw [h] at this
  omega

theorem getElem_ne {i : ℕ} (hi : i < arr.size) : arr[i] ≠ u :=
  fun h => ctx.id_ne hi (by rw [h])

/-- The id tiebreak against `u`, in the form tested by the algorithm: if `arr[i]`'s
client does not win, then `u.id < arr[i].id` (same client: `u` has the larger
clock by `maximal`). -/
theorem u_id_lt {i : ℕ} (hi : i < arr.size) (h : ¬ arr[i].id.clientId < u.id.clientId) :
    u.id < arr[i].id := by
  by_cases hc : u.id.clientId = arr[i].id.clientId
  · exact YjsId.lt_of_clientId_eq hc (ctx.maximal arr[i] (by simp [ArrSet]) hc.symm)
  · exact YjsId.lt_of_clientId_lt (ClientId.lt_of_not_lt_of_ne h hc)

/-- Key order lemma for the scan.  An element `arr[i]` strictly between `u.origin`
and `u.rightOrigin` whose origin is below `u` is itself below `u`, provided its
origin is not to the left of `u.origin` and, in the equal-origin case, it wins the
id tiebreak.  (Paper: rules Lt-RightOrigin, Conflict-DiffOrigin and
Conflict-SameOrigin.) -/
theorem getElem_lt_u {i : ℕ} {oLeftIdx : ℤ} (hi : i < arr.size) (hli : leftIdx < i)
    (hir : i < rightIdx)
    (hoLeft : findPtrIdx arr[i].origin arr = Except.ok oLeftIdx)
    (h_origin_lt : YjsLt' (A := A) arr[i].origin u)
    (h_cases : leftIdx < oLeftIdx ∨ (oLeftIdx = leftIdx ∧ arr[i].id < u.id)) :
    YjsLt' (A := A) arr[i] u := by
  have h_lt_ro : YjsLt' (A := A) arr[i] u.rightOrigin := ctx.getElem_lt_rightOrigin hi hir
  rcases YjsLeq'_or_YjsLt' ctx.setInv ctx.closed (ctx.getElem_rightOrigin_mem hi) u_mem
    with hle | hlt
  · -- `arr[i].rightOrigin ≤ u`: Lt-RightOrigin.
    generalize arr[i] = o at *
    obtain ⟨ oo, orr, oid, oc ⟩ := o
    exact YjsLt'.ltRightOrigin _ _ _ _ _ hle
  · rcases h_cases with hlt_idx | ⟨ heq_idx, hid ⟩
    · -- Different origins, `u.origin < arr[i].origin`: Conflict-DiffOrigin.
      have h_origin_lt' : YjsLt' (A := A) u.origin arr[i].origin :=
        findPtrIdx_lt_YjsLt' arr _ _ ctx.arrInv ctx.left hoLeft hlt_idx
      apply YjsLt'.ltConflict
      generalize arr[i] = o at *
      obtain ⟨ oo, orr, oid, oc ⟩ := o
      obtain ⟨ uo, ur, uid, uc ⟩ := u
      exact ConflictLt'.ltOriginDiff _ _ _ _ _ _ _ _ h_origin_lt' h_lt_ro h_origin_lt hlt
    · -- Same origin, `arr[i].id < u.id`: Conflict-SameOrigin.
      subst heq_idx
      have h_origin_eq : arr[i].origin = u.origin := findPtrIdx_eq_ok_inj _ _ hoLeft ctx.left
      apply YjsLt'.ltConflict
      generalize arr[i] = o at *
      obtain ⟨ oo, orr, oid, oc ⟩ := o
      obtain ⟨ uo, ur, uid, uc ⟩ := u
      simp at h_origin_eq
      subst h_origin_eq
      exact ConflictLt'.ltOriginSame _ _ _ _ _ _ _ h_lt_ro hlt hid

/-! ### Positions versus ids

The set-based scan compares origins by id (`YjsPtr.id?`) and tests membership in id
lists, while the step lemmas speak about positions.  The following lemmas translate. -/

/-- Origins are never `last`. -/
theorem origin_ne_last {i : ℕ} (hi : i < arr.size) : arr[i].origin ≠ YjsPtr.last := by
  intro h
  obtain ⟨ k, hlt ⟩ := YjsLt'.origin_lt_self arr[i]
  rw [h] at hlt
  exact not_last_lt_ptr ctx.closed ctx.setInv k _ (getElem_mem hi) hlt

theorem u_origin_ne_last : u.origin ≠ YjsPtr.last := by
  intro h
  obtain ⟨ k, hlt ⟩ := YjsLt'.origin_lt_self u
  rw [h] at hlt
  exact not_last_lt_ptr ctx.closed ctx.setInv k _ u_mem hlt

/-- Right origins are never `first`. -/
theorem rightOrigin_ne_first {i : ℕ} (hi : i < arr.size) : arr[i].rightOrigin ≠ YjsPtr.first := by
  intro h
  obtain ⟨ k, hlt ⟩ := YjsLt'.self_lt_rightOrigin arr[i]
  rw [h] at hlt
  exact not_ptr_lt_first ctx.closed ctx.setInv k _ (getElem_mem hi) hlt

theorem u_rightOrigin_ne_first : u.rightOrigin ≠ YjsPtr.first := by
  intro h
  obtain ⟨ k, hlt ⟩ := YjsLt'.self_lt_rightOrigin u
  rw [h] at hlt
  exact not_ptr_lt_first ctx.closed ctx.setInv k _ u_mem hlt

/-- Every pointer of the array has a position. -/
theorem exists_findPtrIdx {p : YjsPtr A} (hp : ArrSet arr.toList p) :
    ∃ k, findPtrIdx p arr = Except.ok k := by
  cases p with
  | first => exact ⟨ -1, rfl ⟩
  | last => exact ⟨ arr.size, rfl ⟩
  | itemPtr x =>
    obtain ⟨ n, hn, rfl ⟩ := Array.mem_iff_getElem.1 (by simpa [ArrSet] using hp)
    exact ⟨ n, ctx.findPtrIdx_getElem hn ⟩

theorem exists_origin_idx {i : ℕ} (hi : i < arr.size) :
    ∃ k, findPtrIdx arr[i].origin arr = Except.ok k :=
  ctx.exists_findPtrIdx (origin_p_valid ctx.arrInv.closed _ (by simp [ArrSet]))

theorem exists_rightOrigin_idx {i : ℕ} (hi : i < arr.size) :
    ∃ k, findPtrIdx arr[i].rightOrigin arr = Except.ok k :=
  ctx.exists_findPtrIdx (right_origin_p_valid ctx.arrInv.closed _ (by simp [ArrSet]))

/-- Two pointers of the array that are both origins (never `last`) or both right
origins (never `first`) refer to the same id iff they sit at the same position. -/
theorem id?_eq_iff {p q : YjsPtr A} {k l : ℤ}
    (hk : findPtrIdx p arr = Except.ok k) (hl : findPtrIdx q arr = Except.ok l)
    (hsent : (p ≠ YjsPtr.last ∧ q ≠ YjsPtr.last) ∨ (p ≠ YjsPtr.first ∧ q ≠ YjsPtr.first)) :
    p.id? = q.id? ↔ k = l := by
  cases p with
  | first =>
    simp [findPtrIdx, pure, Except.pure] at hk
    subst hk
    cases q with
    | first => simp [findPtrIdx, pure, Except.pure] at hl; subst hl; simp
    | last => simp at hsent
    | itemPtr b =>
      obtain ⟨ m, hm, rfl, rfl ⟩ := findPtrIdx_itemPtr_eq_ok hl
      constructor
      · intro h; cases h
      · intro h; omega
  | last =>
    simp [findPtrIdx, pure, Except.pure] at hk
    subst hk
    cases q with
    | first => simp at hsent
    | last => simp [findPtrIdx, pure, Except.pure] at hl; subst hl; simp
    | itemPtr b =>
      obtain ⟨ m, hm, rfl, rfl ⟩ := findPtrIdx_itemPtr_eq_ok hl
      constructor
      · intro h; cases h
      · intro h; omega
  | itemPtr a =>
    obtain ⟨ n, hn, rfl, rfl ⟩ := findPtrIdx_itemPtr_eq_ok hk
    cases q with
    | first =>
      simp [findPtrIdx, pure, Except.pure] at hl
      subst hl
      constructor
      · intro h; cases h
      · intro h; omega
    | last =>
      simp [findPtrIdx, pure, Except.pure] at hl
      subst hl
      constructor
      · intro h; cases h
      · intro h; omega
    | itemPtr b =>
      obtain ⟨ m, hm, rfl, rfl ⟩ := findPtrIdx_itemPtr_eq_ok hl
      simp only [YjsPtr.id?, Option.some.injEq]
      constructor
      · intro h
        have heq := ctx.setInv.id_unique _ _ h (getElem_mem hn) (getElem_mem hm)
        have h1 := ctx.findPtrIdx_getElem hn
        rw [heq, ctx.findPtrIdx_getElem hm] at h1
        exact (Except.ok.inj h1).symm
      · intro h
        obtain rfl : n = m := by omega
        rfl

/-- The same-origin test of the scan, as a position test. -/
theorem origin_id?_eq_iff {i : ℕ} {oLeftIdx : ℤ} (hi : i < arr.size)
    (hoLeft : findPtrIdx arr[i].origin arr = Except.ok oLeftIdx) :
    arr[i].origin.id? = u.origin.id? ↔ oLeftIdx = leftIdx :=
  ctx.id?_eq_iff hoLeft ctx.left (Or.inl ⟨ ctx.origin_ne_last hi, ctx.u_origin_ne_last ⟩)

/-- The same-right-origin test of the scan, as a position test. -/
theorem rightOrigin_id?_eq_iff {i : ℕ} {oRightIdx : ℤ} (hi : i < arr.size)
    (hoRight : findPtrIdx arr[i].rightOrigin arr = Except.ok oRightIdx) :
    arr[i].rightOrigin.id? = u.rightOrigin.id? ↔ oRightIdx = rightIdx :=
  ctx.id?_eq_iff hoRight ctx.right
    (Or.inr ⟨ ctx.rightOrigin_ne_first hi, ctx.u_rightOrigin_ne_first ⟩)

/-- An element's origin sits strictly before it. -/
theorem origin_idx_lt {i : ℕ} {oLeftIdx : ℤ} (hi : i < arr.size)
    (hoLeft : findPtrIdx arr[i].origin arr = Except.ok oLeftIdx) : oLeftIdx < i :=
  YjsLt'_findPtrIdx_lt _ _ _ _ _ ctx.arrInv (findPtrIdx_ArrSet hoLeft) (by simp [ArrSet])
    (YjsLt'.origin_lt_self _) hoLeft (ctx.findPtrIdx_getElem hi)

/-- A sentinel origin is `first`, at position `-1`. -/
theorem origin_id?_none {i : ℕ} {oLeftIdx : ℤ} (hi : i < arr.size)
    (hoLeft : findPtrIdx arr[i].origin arr = Except.ok oLeftIdx)
    (h : arr[i].origin.id? = none) : oLeftIdx = -1 := by
  have hne := ctx.origin_ne_last hi
  cases ho : arr[i].origin with
  | first =>
    rw [ho] at hoLeft
    simp [findPtrIdx, pure, Except.pure] at hoLeft
    omega
  | last => exact absurd ho hne
  | itemPtr c =>
    rw [ho] at h
    cases h

/-- Membership of an origin's id in a window id-list is a position test. -/
theorem mem_idsOfRange_iff {i : ℕ} {oLeftIdx : ℤ} {oid : YjsId} {lo : ℤ} {hi' : ℕ}
    {l : List YjsId} (hi : i < arr.size)
    (hoLeft : findPtrIdx arr[i].origin arr = Except.ok oLeftIdx)
    (h : arr[i].origin.id? = some oid) (hl : IdsOfRange arr lo hi' l) :
    oid ∈ l ↔ lo ≤ oLeftIdx ∧ oLeftIdx < hi' := by
  cases ho : arr[i].origin with
  | first => rw [ho] at h; cases h
  | last => rw [ho] at h; cases h
  | itemPtr c =>
    rw [ho] at h hoLeft
    simp only [YjsPtr.id?, Option.some.injEq] at h
    subst h
    obtain ⟨ n, hn, rfl, rfl ⟩ := findPtrIdx_itemPtr_eq_ok hoLeft
    rw [hl]
    constructor
    · rintro ⟨ m, h1, h2, hm, hid ⟩
      have heq := ctx.setInv.id_unique _ _ hid (getElem_mem hm) (getElem_mem hn)
      have h1' := ctx.findPtrIdx_getElem hm
      rw [heq, ctx.findPtrIdx_getElem hn] at h1'
      obtain rfl : n = m := by exact_mod_cast (Except.ok.inj h1')
      exact ⟨ h1, by exact_mod_cast h2 ⟩
    · rintro ⟨ h1, h2 ⟩
      exact ⟨ n, h1, by exact_mod_cast h2, hn, rfl ⟩

/-- The loop's membership test `idMem` of an origin in a window id-list is a position
test.  The window starts at a non-negative position, so the sentinel `first` (position
`-1`, `idMem` false) is handled uniformly. -/
theorem idMem_idsOfRange_iff {i : ℕ} {oLeftIdx : ℤ} {lo : ℤ} {hi' : ℕ} {l : List YjsId}
    (hi : i < arr.size) (hoLeft : findPtrIdx arr[i].origin arr = Except.ok oLeftIdx)
    (hlo : 0 ≤ lo) (hl : IdsOfRange arr lo hi' l) :
    idMem arr[i].origin.id? l = true ↔ lo ≤ oLeftIdx ∧ oLeftIdx < hi' := by
  cases h : arr[i].origin.id? with
  | none =>
    have := ctx.origin_id?_none hi hoLeft h
    simp only [idMem, Bool.false_eq_true, false_iff]
    omega
  | some oid =>
    simp only [idMem, decide_eq_true_eq]
    exact ctx.mem_idsOfRange_iff hi hoLeft h hl

end IntegrateCtx

/-! ## The integration invariant -/

/-- Paper-aligned integration loop invariant for `findIntegratedIndex`.
Parameters:
- `d`: candidate destination index. Items before `d` are confirmed less than `u`.
- `i`: current scan position. Items in `[d, i)` are pending (their order against
  `u` is not yet resolved).
- `scanning`: in same-origin competition mode (extending the pending region for
  the same-origin case).
- `done`: scan has terminated (either by `break` or by reaching `rightIdx`).

Mirrors the paper's Definition (\\S Insert Algorithm and Commutativity). -/
structure IntegrationInvariant (arr : Array (YjsItem A)) (u : YjsItem A)
    (d i : ℕ) (scanning done : Bool) : Prop where
  /-- All items before the candidate destination are strictly smaller than `u`. -/
  prefixLt : ∀ j, j < d → (hj : j < arr.size) → YjsLt' (A := A) arr[j] u
  /-- Each pending item in `[d, i)` either shares origin with `u` (and lost the
  ID tiebreak) or has an origin reachable above `arr[d]`. -/
  scannedRegion : ∀ j, d ≤ j → j < i →
    ∃ (hj : j < arr.size) (hd : d < arr.size),
      (arr[j].origin = u.origin ∧ u.id < arr[j].id) ∨
      YjsLeq' (A := A) (YjsPtr.itemPtr arr[d]) arr[j].origin
  /-- Same-origin competition mode: `arr[d]` shares its origin with `u`. -/
  scanningOrigin : scanning → ∃ (hd : d < arr.size), arr[d].origin = u.origin
  /-- On termination, `u` is strictly smaller than the boundary item `arr[i]`. -/
  doneLt : done → (hi : i < arr.size) → YjsLt' (A := A) u arr[i]

/-- `d` is the position at which `u` has to be inserted to keep `arr` sorted:
everything before `d` is below `u`, and the element at `d` (if any) is above `u`. -/
structure SortedInsertPos (arr : Array (YjsItem A)) (u : YjsItem A) (d : ℕ) : Prop where
  le_size : d ≤ arr.size
  before_lt : ∀ j, j < d → (hj : j < arr.size) → YjsLt' (A := A) arr[j] u
  lt_after : (hd : d < arr.size) → YjsLt' (A := A) u arr[d]

/-- Pending propagation (paper Lemma): if at scan position `i` the
`IntegrationInvariant` holds and `u <_Y arr[i]`, then `u <_Y arr[j]`
for every pending position `j ∈ [d, i]`. -/
theorem pending_propagation
  (arr : Array (YjsItem A)) (u : YjsItem A)
  (leftIdx rightIdx : ℤ) (d i : ℕ)
  (hclosed : IsClosedItemSet (ArrSet (u :: arr.toList)))
  (hinv : ItemSetInvariant (ArrSet (u :: arr.toList)))
  (harrinv : YjsArrInvariant arr.toList)
  (hleftIdx : findPtrIdx u.origin arr = Except.ok leftIdx)
  (hrightIdx : findPtrIdx u.rightOrigin arr = Except.ok rightIdx)
  (hi_le_ri : ↑i ≤ rightIdx)
  (hscanned : ∀ j, d ≤ j → j < i →
    ∃ (hj : j < arr.size) (hd : d < arr.size),
      (arr[j].origin = u.origin ∧ u.id < arr[j].id) ∨
      YjsLeq' (A := A) (YjsPtr.itemPtr arr[d]) arr[j].origin)
  (hi_le : i ≤ arr.size)
  (hi_lt : (h : i < arr.size) → YjsLt' (A := A) u arr[i]) :
  ∀ j : ℕ, d ≤ j → j ≤ i → (h_j_size : j < arr.size) →
    YjsLt' (A := A) u arr[j] := by
  intros j h_j_d h_j_i h_j_size
  generalize hsize : arr[j].size = size
  revert j
  apply Nat.strongRec' (p := fun size => ∀ (j : ℕ),
    d ≤ j → (h_j_i : j ≤ i) → (h_j_size : j < arr.size) →
    arr[j].size = size → YjsLt' (A := A) u (YjsPtr.itemPtr arr[j]))
  intros n ih j h_j_d h_j_i h_j_size heq_n
  wlog h_j_i : j < i
  case inr =>
    have h_j_eq : j = i := by omega
    subst j; exact hi_lt h_j_size
  subst heq_n
  obtain ⟨ h_j_lt_size, h_d_lt_size, h_tbd ⟩ := hscanned j (by omega) h_j_i
  cases h_tbd with
  | inl h_origin =>
    obtain ⟨ h_origin_eq, h_id_lt ⟩ := h_origin
    have ⟨ _, hlt_ro ⟩ : YjsLt' (A := A) u arr[j].rightOrigin := by
      generalize h_ro_eq : arr[j].rightOrigin = ro
      cases ro with
      | first =>
        apply not_rightOrigin_first _ arr[j] hclosed hinv at h_ro_eq
        contradiction
        simp [ArrSet]
      | last =>
        constructor
        apply YjsLt.ltOriginOrder
        apply OriginLt.lt_last
      | itemPtr ro =>
        have ⟨ roIdx, h_ro_in ⟩ : ∃ k : Fin arr.size, arr[k] = ro := by
          cases arr_set_closed_exists_index_for_right_origin arr.toList arr[j] (harrinv.closed) (by simp [ArrSet]) with
          | inl h1 => rw [h_ro_eq] at h1; cases h1
          | inr h =>
            cases h with
            | inl h1 => rw [h_ro_eq] at h1; cases h1
            | inr h1 =>
              rw [h_ro_eq] at h1
              obtain ⟨ k, h1 ⟩ := h1; cases h1; exists k
        have hsize : ro.size < arr[j].size := by
          revert h_ro_eq
          obtain ⟨ o, r, id, c ⟩ := arr[j]; simp
          intros h_ro_eq; subst h_ro_eq
          simp [YjsItem.size, YjsPtr.size]; omega
        have h_d_k : d ≤ roIdx := by
          obtain ⟨ roIdx, _ ⟩ := roIdx; simp at *
          have hlt : j < roIdx := by
            have hlt : YjsLt' (A := A) arr[j] arr[roIdx] := by
              rw [h_ro_in]
              generalize heq : arr[j] = arrj at *
              obtain ⟨ o, r, id, c ⟩ := arrj
              simp at h_ro_eq; subst h_ro_eq
              exists 1
              apply YjsLt.ltRightOrigin; apply YjsLeq.leqSame
            apply getElem_YjsLt'_index_lt arr j roIdx harrinv (by omega) (by omega) hlt
          omega
        cases Nat.lt_or_ge roIdx i with
        | inl h_k_i =>
          obtain x := ih (ro.size) hsize roIdx (by omega) (by omega) (by omega) (by rw [←h_ro_in]; simp)
          simp at h_ro_in x; rw [h_ro_in] at x; assumption
        | inr h_k_i =>
          have h_roIdx_lt : (roIdx : ℕ) < arr.size := roIdx.isLt
          have hlt : YjsLeq' (A := A) arr[i] ro := by
            subst h_ro_in
            apply getElem_leq_YjsLeq' arr i roIdx harrinv (by omega) (by omega)
          apply yjs_leq'_p_trans2 hinv _ _ _ _ _ _ hclosed (hi_lt (by omega)) hlt
          · simp [ArrSet]
          · simp [ArrSet]
          · subst ro; simp [ArrSet]
    have ⟨ _, hlt_ro' ⟩ : YjsLt' (A := A) arr[j] u.rightOrigin := by
      have hlt : ↑j < rightIdx := by omega
      have heq : findPtrIdx (A := A) arr[j] arr = Except.ok ↑j := by
        apply findPtrIdx_getElem; assumption
      apply findPtrIdx_lt_YjsLt' _ _ _ harrinv heq hrightIdx hlt
    obtain ⟨ o, r, id, c ⟩ := u
    generalize arr[j] = item at *
    obtain ⟨ oo, or, oid, oc ⟩ := item
    simp at h_origin_eq hlt_ro hlt_ro'
    rw [h_origin_eq]; rw [h_origin_eq] at hlt_ro'
    constructor
    apply YjsLt.ltConflict
    apply ConflictLt.ltOriginSame <;> try assumption
  | inr hleq =>
    have hlt_ro : YjsLt' (A := A) u arr[j].origin := by
      generalize h_o_eq : arr[j].origin = o
      cases o with
      | first =>
        rw [h_o_eq] at hleq
        apply yjs_leq'_imp_eq_or_yjs_lt' at hleq
        cases hleq with
        | inl heq => cases heq
        | inr hlt =>
          by_contra
          apply not_ptr_lt'_first hclosed hinv at hlt; assumption
          simp [ArrSet]
      | last =>
        constructor; apply YjsLt.ltOriginOrder; apply OriginLt.lt_last
      | itemPtr o =>
        have ⟨ ⟨ oIdx, h_oIdx_lt ⟩, h_o_in ⟩ : ∃ k : Fin arr.size, arr[k] = o := by
          cases arr_set_closed_exists_index_for_origin arr.toList arr[j] (harrinv.closed) (by simp [ArrSet]) with
          | inl h1 => rw [h_o_eq] at h1; cases h1
          | inr h =>
            cases h with
            | inl h1 => rw [h_o_eq] at h1; cases h1
            | inr h1 =>
              rw [h_o_eq] at h1
              obtain ⟨ k, h1 ⟩ := h1; cases h1; exists k
        have hsize : o.size < arr[j].size := by
          revert h_o_eq
          obtain ⟨ o, r, id, c ⟩ := arr[j]; simp
          intros h_o_eq; subst h_o_eq
          simp [YjsItem.size, YjsPtr.size]; omega
        have h_d_k : d ≤ oIdx := by
          suffices h : (↑d : ℤ) ≤ ↑oIdx by omega
          subst h_o_in
          rw [h_o_eq] at hleq
          have hleq' : YjsLeq' (A := A) (YjsPtr.itemPtr arr[d]) (YjsPtr.itemPtr arr[oIdx]) := hleq
          apply YjsLeq'_findPtrIdx_leq _ _ _ _ _ harrinv _ _ hleq'
          · rw [findPtrIdx_getElem _ _ harrinv]
          · rw [findPtrIdx_getElem _ _ harrinv]
          · simp [ArrSet]
          · simp [ArrSet]
        simp at h_o_in; subst h_o_in
        apply ih arr[oIdx].size hsize _ (by omega)
        · simp
        · have hlt : oIdx < j := by
            apply getElem_YjsLt'_index_lt arr oIdx j harrinv (by omega) (by omega)
            rw [←h_o_eq]
            generalize heq : arr[j] = arrj at *
            obtain ⟨ o, r, id, c ⟩ := arrj; simp
            apply YjsLt'.ltOrigin; apply YjsLeq'.leqSame
          omega
    generalize heq : arr[j] = arrj at *
    obtain ⟨ o, r, id, c ⟩ := arrj
    apply YjsLt'.ltOrigin (A := A)
    simp at hlt_ro
    apply YjsLeq'.leqLt; assumption

/-! ## Establishing and preserving the invariant

One lemma per branch of the loop body of `findIntegratedIndex`.  Throughout,
`i` is the scan position (`arr[i]` is the element being examined), `oLeftIdx` and
`oRightIdx` are the positions of its origin and right origin, and the invariant
holds with `done = false` before the step. -/

namespace IntegrationInvariant

variable {arr : Array (YjsItem A)} {u : YjsItem A} {leftIdx rightIdx : ℤ}
  (ctx : IntegrateCtx arr u leftIdx rightIdx)

include ctx

/-- Loop entry: `d = i = leftIdx + 1`, nothing pending, not scanning.  The confirmed
prefix consists of the elements up to and including `u.origin`. -/
theorem init : IntegrationInvariant arr u (leftIdx + 1).toNat (leftIdx + 1).toNat false false where
  prefixLt := fun j hj hj' => by
    have h : YjsLeq' (A := A) arr[j] u.origin :=
      findPtrIdx_leq_YjsLeq' arr _ _ ctx.arrInv (ctx.findPtrIdx_getElem hj') ctx.left (by omega)
    obtain ⟨ o, r, id, c ⟩ := u
    exact YjsLt'.ltOrigin _ _ _ _ _ h
  scannedRegion := fun j h1 h2 => absurd h2 (by omega)
  scanningOrigin := fun h => by cases h
  doneLt := fun h => by cases h

/-- Branch 1 (`oLeftIdx < leftIdx`, lines 9–10): the loop exits; the examined element
is above `u`.  Otherwise `arr[i] < u`, and the no-cross-origin lemma would put
`arr[i].origin` at or after `u.origin`, or `arr[i]` at or before `u.origin`. -/
theorem step_break_left {d i : ℕ} {scanning : Bool} {oLeftIdx : ℤ}
    (hi : i < arr.size) (hli : leftIdx < i)
    (hoLeft : findPtrIdx arr[i].origin arr = Except.ok oLeftIdx) (h : oLeftIdx < leftIdx)
    (hinv : IntegrationInvariant arr u d i scanning false) :
    IntegrationInvariant arr u d i scanning true where
  prefixLt := hinv.prefixLt
  scannedRegion := hinv.scannedRegion
  scanningOrigin := hinv.scanningOrigin
  doneLt := fun _ _ => by
    rcases YjsLeq'_or_YjsLt' ctx.setInv ctx.closed (IntegrateCtx.getElem_mem hi)
      IntegrateCtx.u_mem with hle | hlt
    · exfalso
      rcases yjs_leq'_imp_eq_or_yjs_lt' hle with heq | hlt
      · exact ctx.getElem_ne hi (by injection heq)
      · rcases no_cross_origin ctx.closed ctx.setInv (IntegrateCtx.getElem_mem hi)
          IntegrateCtx.u_mem hlt with h1 | h2
        · have := YjsLeq'_findPtrIdx_leq _ _ _ _ _ ctx.arrInv (findPtrIdx_ArrSet ctx.left)
            (findPtrIdx_ArrSet hoLeft) h1 ctx.left hoLeft
          omega
        · have := YjsLeq'_findPtrIdx_leq _ _ _ _ _ ctx.arrInv (by simp [ArrSet])
            (findPtrIdx_ArrSet ctx.left) h2 (ctx.findPtrIdx_getElem hi) ctx.left
          omega
    · exact hlt

/-- Branch 2 (same origin, `u` wins the client tiebreak, lines 12–13): `arr[i]`
joins the confirmed prefix, by Conflict-SameOrigin. -/
theorem step_advance_same {d i : ℕ} {scanning : Bool} {oLeftIdx : ℤ}
    (hi : i < arr.size) (hli : leftIdx < i) (hir : i < rightIdx)
    (hoLeft : findPtrIdx arr[i].origin arr = Except.ok oLeftIdx) (h : oLeftIdx = leftIdx)
    (hid : arr[i].id.clientId < u.id.clientId)
    (hinv : IntegrationInvariant arr u d i scanning false) :
    IntegrationInvariant arr u (i + 1) (i + 1) false false where
  prefixLt := fun j hj hj' => by
    subst h
    have h_origin_eq : arr[i].origin = u.origin := findPtrIdx_eq_ok_inj _ _ hoLeft ctx.left
    have h_i_lt : YjsLt' (A := A) arr[i] u :=
      ctx.getElem_lt_u hi hli hir hoLeft (h_origin_eq ▸ YjsLt'.origin_lt_self u)
        (Or.inr ⟨ rfl, YjsId.lt_of_clientId_lt hid ⟩)
    rcases Nat.lt_or_ge j d with hjd | hjd
    · exact hinv.prefixLt j hjd hj'
    · exact yjs_leq'_p_trans1 ctx.setInv _ _ _ (IntegrateCtx.getElem_mem hj')
        (IntegrateCtx.getElem_mem hi) IntegrateCtx.u_mem ctx.closed
        (ctx.getElem_le (by omega) hi) h_i_lt
  scannedRegion := fun j h1 h2 => absurd h2 (by omega)
  scanningOrigin := fun h => by cases h
  doneLt := fun h => by cases h

/-- Branch 3 (same origin and same right origin, `u` loses the tiebreak,
lines 14–15): the loop exits with `u < arr[i]` by Conflict-SameOrigin. -/
theorem step_break_same_right {d i : ℕ} {scanning : Bool} {oLeftIdx oRightIdx : ℤ}
    (hi : i < arr.size)
    (hoLeft : findPtrIdx arr[i].origin arr = Except.ok oLeftIdx) (h : oLeftIdx = leftIdx)
    (hid : ¬ arr[i].id.clientId < u.id.clientId)
    (hoRight : findPtrIdx arr[i].rightOrigin arr = Except.ok oRightIdx) (hr : oRightIdx = rightIdx)
    (hinv : IntegrationInvariant arr u d i scanning false) :
    IntegrationInvariant arr u d i scanning true where
  prefixLt := hinv.prefixLt
  scannedRegion := hinv.scannedRegion
  scanningOrigin := hinv.scanningOrigin
  doneLt := fun _ _ => by
    subst h hr
    have ho : arr[i].origin = u.origin := findPtrIdx_eq_ok_inj _ _ hoLeft ctx.left
    have hro : arr[i].rightOrigin = u.rightOrigin := findPtrIdx_eq_ok_inj _ _ hoRight ctx.right
    have hidlt : u.id < arr[i].id := ctx.u_id_lt hi hid
    apply YjsLt'.ltConflict
    generalize arr[i] = o at *
    obtain ⟨ oo, orr, oid, oc ⟩ := o
    obtain ⟨ uo, ur, uid, uc ⟩ := u
    simp at ho hro
    subst ho hro
    exact ConflictLt'.ltOriginSame _ _ _ _ _ _ _
      (YjsLt'.self_lt_rightOrigin _) (YjsLt'.self_lt_rightOrigin _) hidlt

/-- Branch 4 (same origin, different right origin, `u` loses the tiebreak,
lines 16–17): `arr[i]` becomes pending under clause (a) and scanning starts. -/
theorem step_pending_same {d i : ℕ} {scanning : Bool} {oLeftIdx : ℤ}
    (hi : i < arr.size)
    (hoLeft : findPtrIdx arr[i].origin arr = Except.ok oLeftIdx) (h : oLeftIdx = leftIdx)
    (hid : ¬ arr[i].id.clientId < u.id.clientId)
    (hinv : IntegrationInvariant arr u d i scanning false) (hdi : d ≤ i)
    (hd_eq : scanning = false → d = i) :
    IntegrationInvariant arr u d (i + 1) true false where
  prefixLt := hinv.prefixLt
  scannedRegion := fun j h1 h2 => by
    rcases Nat.lt_or_ge j i with hj | hj
    · exact hinv.scannedRegion j h1 hj
    · have hji : j = i := by omega
      subst hji
      refine ⟨ hi, by omega, Or.inl ⟨ ?_, ctx.u_id_lt hi hid ⟩ ⟩
      subst h
      exact findPtrIdx_eq_ok_inj _ _ hoLeft ctx.left
  scanningOrigin := fun _ => by
    cases hs : scanning
    · have hdi' := hd_eq hs
      subst hdi' h
      exact ⟨ hi, findPtrIdx_eq_ok_inj _ _ hoLeft ctx.left ⟩
    · exact hinv.scanningOrigin hs
  doneLt := fun h => by cases h

/-- Branch 5 (greater origin, not scanning): `arr[i]` joins the confirmed prefix.
Its origin sits at an index below `d = i`, hence below `u`, and `getElem_lt_u`
concludes. -/
theorem step_advance_other {d i : ℕ} {scanning : Bool} {oLeftIdx : ℤ}
    (hi : i < arr.size) (hli : leftIdx < i) (hir : i < rightIdx)
    (hoLeft : findPtrIdx arr[i].origin arr = Except.ok oLeftIdx) (h : leftIdx < oLeftIdx)
    (hs : scanning = false)
    (hinv : IntegrationInvariant arr u d i scanning false) (hdi : d = i) :
    IntegrationInvariant arr u (i + 1) (i + 1) scanning false where
  prefixLt := fun j hj hj' => by
    subst hdi hs
    have hk_lt : oLeftIdx < d :=
      YjsLt'_findPtrIdx_lt _ _ _ _ _ ctx.arrInv (findPtrIdx_ArrSet hoLeft) (by simp [ArrSet])
        (YjsLt'.origin_lt_self _) hoLeft (ctx.findPtrIdx_getElem hi)
    have hl := ctx.left_ge
    have hk_size : oLeftIdx.toNat < arr.size := by omega
    have h_origin_eq : (arr[oLeftIdx.toNat] : YjsPtr A) = arr[d].origin :=
      findPtrIdx_lt_size_getElem hoLeft (by omega) hk_size
    have h_origin_lt : YjsLt' (A := A) arr[d].origin u := by
      rw [← h_origin_eq]
      exact hinv.prefixLt _ (by omega) hk_size
    have h_i_lt : YjsLt' (A := A) arr[d] u := ctx.getElem_lt_u hi hli hir hoLeft h_origin_lt (Or.inl h)
    exact yjs_leq'_p_trans1 ctx.setInv _ _ _ (IntegrateCtx.getElem_mem hj')
      (IntegrateCtx.getElem_mem hi) IntegrateCtx.u_mem ctx.closed
      (ctx.getElem_le (by omega) hi) h_i_lt
  scannedRegion := fun j h1 h2 => absurd h2 (by omega)
  scanningOrigin := fun h => by subst hs; cases h
  doneLt := fun h => by cases h

/-- Branch 6 (greater origin, scanning): `arr[i]` becomes pending under clause (b).
`arr[d] < arr[i]` by sortedness (they differ because their origins do), and the
no-cross-origin lemma gives `arr[d] ≤ arr[i].origin`. -/
theorem step_pending_other {d i : ℕ} {scanning : Bool} {oLeftIdx : ℤ}
    (hi : i < arr.size)
    (hoLeft : findPtrIdx arr[i].origin arr = Except.ok oLeftIdx) (h : leftIdx < oLeftIdx)
    (hs : scanning = true)
    (hinv : IntegrationInvariant arr u d i scanning false) (hdi : d ≤ i) :
    IntegrationInvariant arr u d (i + 1) scanning false where
  prefixLt := hinv.prefixLt
  scannedRegion := fun j h1 h2 => by
    rcases Nat.lt_or_ge j i with hj | hj
    · exact hinv.scannedRegion j h1 hj
    · have hji : j = i := by omega
      subst hji
      obtain ⟨ hd, hd_origin ⟩ := hinv.scanningOrigin hs
      refine ⟨ hi, hd, Or.inr ?_ ⟩
      have hle : YjsLeq' (A := A) arr[d] arr[j] := ctx.getElem_le hdi hi
      have hne : arr[d] ≠ arr[j] := by
        intro heq
        have : findPtrIdx arr[j].origin arr = Except.ok leftIdx := by
          rw [← heq, hd_origin]; exact ctx.left
        rw [this] at hoLeft
        cases hoLeft
        omega
      have hlt : YjsLt' (A := A) arr[d] arr[j] := by
        rcases yjs_leq'_imp_eq_or_yjs_lt' hle with heq | hlt
        · exact absurd (by injection heq) hne
        · exact hlt
      rcases no_cross_origin ctx.arrInv.closed ctx.arrInv.item_set_inv (by simp [ArrSet])
        (by simp [ArrSet]) hlt with h1 | h2
      · exfalso
        rw [hd_origin] at h1
        have := YjsLeq'_findPtrIdx_leq _ _ _ _ _ ctx.arrInv (findPtrIdx_ArrSet hoLeft)
          (findPtrIdx_ArrSet ctx.left) h1 hoLeft ctx.left
        omega
      · exact h2
  scanningOrigin := fun _ => hinv.scanningOrigin hs
  doneLt := fun h => by cases h

/-- While scanning, the origin of the examined element never lies below the
destination `d`: by Branch 6 it is at or after `arr[d]`.  This rules out the
set-based scan advancing in scanning mode. -/
theorem dest_le_origin_of_scanning {d i : ℕ} {scanning : Bool} {oLeftIdx : ℤ}
    (hi : i < arr.size)
    (hoLeft : findPtrIdx arr[i].origin arr = Except.ok oLeftIdx) (h : leftIdx < oLeftIdx)
    (hs : scanning = true)
    (hinv : IntegrationInvariant arr u d i scanning false) (hdi : d ≤ i) :
    (d : ℤ) ≤ oLeftIdx := by
  obtain ⟨ _, hd, hcase ⟩ :=
    (step_pending_other ctx hi hoLeft h hs hinv hdi).scannedRegion i hdi (Nat.lt_succ_self i)
  rcases hcase with ⟨ horig, _ ⟩ | hle
  · exfalso
    rw [horig, ctx.left] at hoLeft
    cases hoLeft
    omega
  · exact YjsLeq'_findPtrIdx_leq _ _ _ _ _ ctx.arrInv (by simp [ArrSet]) (findPtrIdx_ArrSet hoLeft)
      hle (ctx.findPtrIdx_getElem hd) hoLeft

/-- At loop exit the invariant determines the sorted insertion position: the
confirmed prefix is below `u`, and pending propagation lifts `u < arr[i]` to every
pending position, in particular to `arr[d]`. -/
theorem toSortedInsertPos {d i : ℕ} {scanning done : Bool}
    (hinv : IntegrationInvariant arr u d i scanning done) (hdi : d ≤ i)
    (hir : (i : ℤ) ≤ rightIdx)
    (hend : (hi : i < arr.size) → YjsLt' (A := A) u arr[i]) : SortedInsertPos arr u d where
  le_size := by have := ctx.right_le; omega
  before_lt := hinv.prefixLt
  lt_after := fun hd =>
    pending_propagation arr u leftIdx rightIdx d i ctx.closed ctx.setInv ctx.arrInv ctx.left
      ctx.right hir hinv.scannedRegion (by have := ctx.right_le; omega) hend d (le_refl _) hdi hd

end IntegrationInvariant

/-! ## Connecting to the executable loop -/

/-- The loop state of `findIntegratedIndex`: `⟨conflictingItems, destIdx, itemsBeforeOrigin⟩`
(`do`-notation orders the mutable variables alphabetically). -/
abbrev ScanState := MProd (List YjsId) (MProd ℤ (List YjsId))

/-- Loop invariant of `findIntegratedIndex` for `mvcgen`.  `pref`/`suff` are the
processed and remaining offsets of the loop range `[1 : rightIdx - leftIdx]`.  Besides
the mathematical `IntegrationInvariant` (with the ghost flag `scanning = (d < i)`), it
records that `itemsBeforeOrigin` is the id list of the scanned window `(leftIdx, i)` and
`conflictingItems` that of the pending region `[d, i)`. -/
def ScanLoopInv (arr : Array (YjsItem A)) (u : YjsItem A) (leftIdx rightIdx : ℤ)
    (pref suff : List ℕ) (st : ScanState) : Prop :=
  ∃ (d i : ℕ) (scanning done : Bool),
    st.snd.fst = (d : ℤ) ∧ d ≤ i ∧ (i : ℤ) ≤ rightIdx ∧
    (done = true → suff = []) ∧
    (done = false → (i : ℤ) = leftIdx + 1 + pref.length) ∧
    (scanning = true ↔ d < i) ∧
    (done = false → IdsOfRange arr (leftIdx + 1) i st.snd.snd) ∧
    (done = false → IdsOfRange arr d i st.fst) ∧
    IntegrationInvariant arr u d i scanning done

namespace ScanLoopInv

variable {arr : Array (YjsItem A)} {u : YjsItem A} {leftIdx rightIdx : ℤ}
  (ctx : IntegrateCtx arr u leftIdx rightIdx)

include ctx

theorem init {xs : List ℕ} : ScanLoopInv arr u leftIdx rightIdx [] xs ⟨[], leftIdx + 1, []⟩ := by
  have hl := ctx.left_ge
  refine ⟨ (leftIdx + 1).toNat, (leftIdx + 1).toNat, false, false, by simp only; omega, le_refl _,
    by have := ctx.left_lt_right; omega, by simp, fun _ => by simp; omega, by simp,
    fun _ => IdsOfRange.nil (by omega), fun _ => IdsOfRange.nil (by omega),
    IntegrationInvariant.init ctx ⟩

/-- Unpacking the invariant at a loop step: the loop has not exited, and the
examined index `(leftIdx + cur).toNat` is the scan position `i`. -/
theorem step_pre {pref suff : List ℕ} {cur : ℕ} {st : ScanState}
    (hlist : List.range' 1 ((rightIdx - leftIdx).toNat - 1) = pref ++ cur :: suff)
    (h : ScanLoopInv arr u leftIdx rightIdx pref (cur :: suff) st) :
    ∃ (d i : ℕ) (scanning : Bool), st.snd.fst = d ∧ d ≤ i ∧ (leftIdx + cur).toNat = i ∧
      leftIdx < i ∧ (i : ℤ) < rightIdx ∧ i < arr.size ∧ (i : ℤ) = leftIdx + 1 + pref.length ∧
      (scanning = true ↔ d < i) ∧
      IdsOfRange arr (leftIdx + 1) i st.snd.snd ∧ IdsOfRange arr d i st.fst ∧
      IntegrationInvariant arr u d i scanning false := by
  obtain ⟨ d, i, scanning, done, hdest, hdi, hir, hdone, hpos, hs, hibo, hci, hinv ⟩ := h
  cases done
  · obtain ⟨ hcur, hlen ⟩ := List.range'_eq_append_cons hlist
    have hpos := hpos rfl
    have hl := ctx.left_ge
    have hr := ctx.right_le
    have hlr := ctx.left_lt_right
    exact ⟨ d, i, scanning, hdest, hdi, by omega, by omega, by omega, by omega, hpos, hs,
      hibo rfl, hci rfl, hinv ⟩
  · exact absurd (hdone rfl) (by simp)

omit ctx [DecidableEq A] in
theorem of_yield {d i : ℕ} {scanning : Bool} {pref suff : List ℕ} {cur : ℕ} {dest : ℤ}
    {ibo ci : List YjsId}
    (hdest : dest = (d : ℤ)) (hinv : IntegrationInvariant arr u d (i + 1) scanning false)
    (hdi : d ≤ i + 1) (hir : (i : ℤ) + 1 ≤ rightIdx) (hpos : (i : ℤ) = leftIdx + 1 + pref.length)
    (hs : scanning = true ↔ d < i + 1)
    (hibo : IdsOfRange arr (leftIdx + 1) (i + 1) ibo) (hci : IdsOfRange arr d (i + 1) ci) :
    ScanLoopInv arr u leftIdx rightIdx (pref ++ [cur]) suff ⟨ci, dest, ibo⟩ :=
  ⟨ d, i + 1, scanning, false, hdest, hdi, by omega, by simp,
    fun _ => by simp; omega, hs, fun _ => hibo, fun _ => hci, hinv ⟩

omit ctx [DecidableEq A] in
theorem of_done {d i : ℕ} {scanning : Bool} {xs : List ℕ} {dest : ℤ} {ibo ci : List YjsId}
    (hdest : dest = (d : ℤ)) (hinv : IntegrationInvariant arr u d i scanning true)
    (hdi : d ≤ i) (hir : (i : ℤ) ≤ rightIdx) (hs : scanning = true ↔ d < i) :
    ScanLoopInv arr u leftIdx rightIdx xs [] ⟨ci, dest, ibo⟩ :=
  ⟨ d, i, scanning, true, hdest, hdi, hir, fun _ => rfl, by simp, hs, by simp, by simp, hinv ⟩

/-- At loop exit the invariant yields the sorted insertion position.  If the loop
ran to completion, the scan position is `rightIdx`, where `u.rightOrigin` sits. -/
theorem exit {st : ScanState}
    (h : ScanLoopInv arr u leftIdx rightIdx (List.range' 1 ((rightIdx - leftIdx).toNat - 1)) [] st) :
    SortedInsertPos arr u st.snd.fst.toNat := by
  obtain ⟨ d, i, scanning, done, hdest, hdi, hir, _, hpos, _, _, _, hinv ⟩ := h
  have hr := ctx.right_le
  have hlr := ctx.left_lt_right
  have hl := ctx.left_ge
  rw [hdest, Int.toNat_natCast]
  apply IntegrationInvariant.toSortedInsertPos ctx hinv hdi hir
  intro hi
  cases done
  · have hpos := hpos rfl
    simp at hpos
    have hi_eq : rightIdx.toNat = i := by omega
    have h_ro : (arr[rightIdx.toNat] : YjsPtr A) = u.rightOrigin :=
      findPtrIdx_lt_size_getElem ctx.right (by omega) (by omega)
    simp only [hi_eq] at h_ro
    rw [h_ro]
    exact YjsLt'.self_lt_rightOrigin u
  · exact hinv.doneLt rfl hi

end ScanLoopInv

/-- Specification of the integration loop: under the integration context, it returns
the sorted insertion position of `u`, the item the input resolves to. -/
@[spec]
theorem findIntegratedIndex_spec (input : IntegrateInput A) {arr : Array (YjsItem A)}
    {u : YjsItem A} {leftIdx rightIdx : ℤ} (ctx : IntegrateCtx arr u leftIdx rightIdx)
    (h_item : input.toItem arr = Except.ok u) :
    ⦃⌜True⌝⦄ findIntegratedIndex leftIdx rightIdx input arr
    ⦃post⟨fun d => ⌜SortedInsertPos arr u d⌝, fun _ => ⌜True⌝⟩⦄ := by
  obtain ⟨ h_id, h_oid, h_rid ⟩ := IntegrateInput.toItem_ids h_item
  unfold findIntegratedIndex
  mvcgen [getElemExcept_spec]
  case inv1 =>
    exact post⟨fun ⟨xs, st⟩ => ⌜ScanLoopInv arr u leftIdx rightIdx xs.prefix xs.suffix st⌝,
      fun _ => ⌜True⌝⟩
  all_goals mleave
  case vc7.step.except.handle => intros; trivial
  case vc8.pre => exact ScanLoopInv.init ctx
  case vc9.post.success =>
    rename_i st h
    rw [Std.Range.toList_one] at h
    exact ScanLoopInv.exit ctx h
  -- Branch 2: same origin, `u` wins the tiebreak, advance.
  case vc1.step.success.isTrue.isTrue =>
    rename_i pref cur suff hlist b x destIdx ibo0 i hex other ibo ci h_eq h_id_lt h_other
    rw [Std.Range.toList_one] at hlist
    rw [h_id] at h_id_lt
    obtain ⟨ d, i', scanning, hdest, hdi, hidx, hli, hir, hi, hpos, hs, hibo, hci, hinv ⟩ :=
      ScanLoopInv.step_pre ctx hlist hex
    have hii : i = i' := hidx
    rw [hii] at h_other ⊢
    obtain ⟨ _, rfl ⟩ := getElemExcept_eq_ok_iff.1 h_other.1
    obtain ⟨ oLeftIdx, hoLeft ⟩ := ctx.exists_origin_idx hi
    have hol : oLeftIdx = leftIdx := (ctx.origin_id?_eq_iff hi hoLeft).1 (h_eq.trans h_oid.symm)
    exact ScanLoopInv.of_yield (by simp)
      (IntegrationInvariant.step_advance_same ctx hi hli hir hoLeft hol h_id_lt hinv) (le_refl _)
      (by omega) hpos (by simp) (IdsOfRange.cons hibo hi (by omega)) (IdsOfRange.nil (le_refl _))
  -- Branch 3: same origin and right origin, `u` loses the tiebreak, break.
  case vc2.step.success.isTrue.isFalse.isTrue =>
    rename_i pref cur suff hlist b x destIdx ibo0 i hex other ibo ci h_eq h_nid h_req h_other
    rw [Std.Range.toList_one] at hlist
    rw [h_id] at h_nid
    obtain ⟨ d, i', scanning, hdest, hdi, hidx, hli, hir, hi, hpos, hs, hibo, hci, hinv ⟩ :=
      ScanLoopInv.step_pre ctx hlist hex
    have hii : i = i' := hidx
    rw [hii] at h_other
    obtain ⟨ _, rfl ⟩ := getElemExcept_eq_ok_iff.1 h_other.1
    obtain ⟨ oLeftIdx, hoLeft ⟩ := ctx.exists_origin_idx hi
    obtain ⟨ oRightIdx, hoRight ⟩ := ctx.exists_rightOrigin_idx hi
    have hol : oLeftIdx = leftIdx := (ctx.origin_id?_eq_iff hi hoLeft).1 (h_eq.trans h_oid.symm)
    have hor : oRightIdx = rightIdx :=
      (ctx.rightOrigin_id?_eq_iff hi hoRight).1 (h_req.trans h_rid.symm)
    exact ScanLoopInv.of_done hdest
      (IntegrationInvariant.step_break_same_right ctx hi hoLeft hol h_nid hoRight hor hinv) hdi
      (by omega) hs
  -- Branch 4: same origin, different right origin, `u` loses the tiebreak, pending.
  case vc3.step.success.isTrue.isFalse.isFalse =>
    rename_i pref cur suff hlist b x destIdx ibo0 i hex other ibo ci h_eq h_nid h_nreq h_other
    rw [Std.Range.toList_one] at hlist
    rw [h_id] at h_nid
    obtain ⟨ d, i', scanning, hdest, hdi, hidx, hli, hir, hi, hpos, hs, hibo, hci, hinv ⟩ :=
      ScanLoopInv.step_pre ctx hlist hex
    have hii : i = i' := hidx
    rw [hii] at h_other
    obtain ⟨ _, rfl ⟩ := getElemExcept_eq_ok_iff.1 h_other.1
    obtain ⟨ oLeftIdx, hoLeft ⟩ := ctx.exists_origin_idx hi
    have hol : oLeftIdx = leftIdx := (ctx.origin_id?_eq_iff hi hoLeft).1 (h_eq.trans h_oid.symm)
    have hnd : scanning = false → d = i' := fun h => by simp [h] at hs; omega
    exact ScanLoopInv.of_yield hdest
      (IntegrationInvariant.step_pending_same ctx hi hoLeft hol h_nid hinv hdi hnd)
      (by omega) (by omega) hpos (by simp; omega) (IdsOfRange.cons hibo hi (by omega))
      (IdsOfRange.cons hci hi (by omega))
  -- Branch 5: greater origin, already scanned and not pending: advance.  In scanning
  -- mode this cannot happen (`dest_le_origin_of_scanning`).
  case vc4.step.success.isFalse.isTrue.isTrue =>
    rename_i pref cur suff hlist b x destIdx ibo0 i hex other ibo ci h_neq h_in h_nin h_other
    rw [Std.Range.toList_one] at hlist
    obtain ⟨ d, i', scanning, hdest, hdi, hidx, hli, hir, hi, hpos, hs, hibo, hci, hinv ⟩ :=
      ScanLoopInv.step_pre ctx hlist hex
    have hii : i = i' := hidx
    rw [hii] at h_other ⊢
    obtain ⟨ _, rfl ⟩ := getElemExcept_eq_ok_iff.1 h_other.1
    obtain ⟨ oLeftIdx, hoLeft ⟩ := ctx.exists_origin_idx hi
    have hibo' := IdsOfRange.cons hibo hi (by omega)
    have hci' := IdsOfRange.cons hci hi (by omega)
    have hl := ctx.left_ge
    have h_gt : leftIdx < oLeftIdx := by
      have := (ctx.idMem_idsOfRange_iff hi hoLeft (by omega) hibo').1 h_in
      omega
    have h_lt_d : oLeftIdx < d := by
      have := mt (ctx.idMem_idsOfRange_iff hi hoLeft (by omega) hci').2 (by simpa using h_nin)
      have := ctx.origin_idx_lt hi hoLeft
      omega
    cases scanning with
    | true =>
      exfalso
      have := IntegrationInvariant.dest_le_origin_of_scanning ctx hi hoLeft h_gt rfl hinv hdi
      omega
    | false =>
      have hdi' : d = i' := by simp at hs; omega
      exact ScanLoopInv.of_yield (by simp)
        (IntegrationInvariant.step_advance_other ctx hi hli hir hoLeft h_gt rfl hinv hdi')
        (le_refl _) (by omega) hpos (by simp) hibo' (IdsOfRange.nil (le_refl _))
  -- Branch 6: greater origin, already scanned and pending: keep scanning.
  case vc5.step.success.isFalse.isTrue.isFalse =>
    rename_i pref cur suff hlist b x destIdx ibo0 i hex other ibo ci h_neq h_in h_nnin h_other
    rw [Std.Range.toList_one] at hlist
    obtain ⟨ d, i', scanning, hdest, hdi, hidx, hli, hir, hi, hpos, hs, hibo, hci, hinv ⟩ :=
      ScanLoopInv.step_pre ctx hlist hex
    have hii : i = i' := hidx
    rw [hii] at h_other
    obtain ⟨ _, rfl ⟩ := getElemExcept_eq_ok_iff.1 h_other.1
    obtain ⟨ oLeftIdx, hoLeft ⟩ := ctx.exists_origin_idx hi
    have hibo' := IdsOfRange.cons hibo hi (by omega)
    have hci' := IdsOfRange.cons hci hi (by omega)
    have hl := ctx.left_ge
    have h_gt : leftIdx < oLeftIdx := by
      have := (ctx.idMem_idsOfRange_iff hi hoLeft (by omega) hibo').1 h_in
      omega
    have h_ge_d : (d : ℤ) ≤ oLeftIdx :=
      ((ctx.idMem_idsOfRange_iff hi hoLeft (by omega) hci').1 (by simpa using h_nnin)).1
    have holt := ctx.origin_idx_lt hi hoLeft
    cases scanning with
    | false =>
      exfalso
      simp at hs
      omega
    | true =>
      exact ScanLoopInv.of_yield hdest
        (IntegrationInvariant.step_pending_other ctx hi hoLeft h_gt rfl hinv hdi)
        (by omega) (by omega) hpos (by simp; omega) hibo' hci'
  -- Branch 1: the origin was not scanned (it precedes `u.origin`, or is `first`): break.
  case vc6.step.success.isFalse.isFalse =>
    rename_i pref cur suff hlist b x destIdx ibo0 i hex other ibo ci h_neq h_nin h_other
    rw [Std.Range.toList_one] at hlist
    obtain ⟨ d, i', scanning, hdest, hdi, hidx, hli, hir, hi, hpos, hs, hibo, hci, hinv ⟩ :=
      ScanLoopInv.step_pre ctx hlist hex
    have hii : i = i' := hidx
    rw [hii] at h_other
    obtain ⟨ _, rfl ⟩ := getElemExcept_eq_ok_iff.1 h_other.1
    obtain ⟨ oLeftIdx, hoLeft ⟩ := ctx.exists_origin_idx hi
    have hibo' := IdsOfRange.cons hibo hi (by omega)
    have hl := ctx.left_ge
    have hne : oLeftIdx ≠ leftIdx := fun h =>
      h_neq (((ctx.origin_id?_eq_iff hi hoLeft).2 h).trans h_oid)
    have h_lt : oLeftIdx < leftIdx := by
      have := mt (ctx.idMem_idsOfRange_iff hi hoLeft (by omega) hibo').2 h_nin
      have := ctx.origin_idx_lt hi hoLeft
      omega
    exact ScanLoopInv.of_done hdest
      (IntegrationInvariant.step_break_left ctx hi hli hoLeft h_lt hinv) hdi (by omega) hs

/-- The scan never fails once the window lies inside the array: its only effect is
reading `arr[i]` for `leftIdx < i < rightIdx`. -/
theorem findIntegratedIndex_ok_of_bounds {leftIdx rightIdx : ℤ} (input : IntegrateInput A)
    (arr : Array (YjsItem A)) (h_left : -1 ≤ leftIdx) (h_right : rightIdx ≤ arr.size) :
    ∃ destIdx, findIntegratedIndex leftIdx rightIdx input arr = Except.ok destIdx := by
  have hP : (match findIntegratedIndex leftIdx rightIdx input arr with
      | Except.ok _ => True
      | Except.error _ => False) := by
    apply Except.of_wp (prog := findIntegratedIndex leftIdx rightIdx input arr)
      (P := fun r => match r with
        | Except.ok _ => True
        | Except.error _ => False)
    unfold findIntegratedIndex
    mvcgen [getElemExcept_spec]
    case inv1 => exact post⟨fun _ => ⌜True⌝, fun _ => ⌜False⌝⟩
    all_goals mleave
    case vc7.step.except.handle =>
      rename_i pref cur suff hlist b x destIdx ibo i _ _
      intro hge
      have hi : i = (leftIdx + cur).toNat := rfl
      rw [Std.Range.toList_one] at hlist
      obtain ⟨ hcur, hlen ⟩ := List.range'_eq_append_cons hlist
      omega
  cases h : findIntegratedIndex leftIdx rightIdx input arr with
  | ok d => exact ⟨ d, rfl ⟩
  | error e => simp [h] at hP

/-! ## Inserting at the sorted position -/

theorem YjsArrInvariant_insertIdxIfInBounds (arr : Array (YjsItem A)) (newItem : YjsItem A) (i : ℕ) :
  IsClosedItemSet (ArrSet $ newItem :: arr.toList)
  -> ItemSetInvariant (ArrSet $ newItem :: arr.toList)
  -> YjsArrInvariant arr.toList
  -> (hisize : i ≤ arr.size)
  -> ((hizero : 0 < i) -> YjsLt' (A := A) arr[i - 1] newItem)
  -> ((hisize : i < arr.size) -> YjsLt' (A := A) newItem arr[i])
  -> (∀ a, a ∈ arr -> a.id ≠ newItem.id)
  -> YjsArrInvariant (arr.insertIdxIfInBounds i newItem).toList := by
  intros hclosed hinv harrinv hisize hlt1 hlt2 hneq
  obtain ⟨ _, _, hsorted, hunique ⟩ := harrinv
  have heqset : ∀ x, ArrSet (newItem :: arr.toList) x ↔ ArrSet (List.insertIdx arr.toList i newItem) x := by
    intros x
    simp only [ArrSet]
    cases x with
    | first => simp
    | last => simp
    | itemPtr x =>
      simp
      rw [List.mem_insertIdx hisize]
      simp

  have heqset' : ∀ x, ArrSet (newItem :: arr.toList) x ↔ ArrSet (arr.insertIdxIfInBounds i newItem).toList x := by
    intros
    rw [List.insertIdxIfInBounds_toArray]
    simp
    rw [heqset]

  have hsubset a : (ArrSet arr.toList) a -> (ArrSet (List.insertIdx arr.toList i newItem)) a := by
    intros hmem
    cases a with
    | first => simp [ArrSet]
    | last => simp [ArrSet]
    | itemPtr a =>
      simp [ArrSet]
      rw [List.mem_insertIdx hisize]
      right
      assumption

  have hsubset' : ∀ x, ArrSet arr.toList x -> ArrSet (newItem :: arr.toList) x := by
    intros a hmem
    simp [ArrSet] at *
    cases a <;> simp
    right
    assumption

  apply YjsArrInvariant.mk
  . apply IsClosedItemSet.eq_set (P := ArrSet $ newItem :: arr.toList) _ hclosed heqset'
  . apply ItemSetInvariant.eq_set (P := ArrSet $ newItem :: arr.toList) _ hclosed hinv heqset'
  . rw [List.insertIdxIfInBounds_toArray]
    simp
    apply List.Pairwise_insertIdx
    . apply List.Pairwise_weaken (R := fun (a b : YjsItem A) => YjsLt' (A := A) a b) <;> try assumption
      intros
      assumption
    . intros j hji
      apply yjs_leq'_p_trans1 (inv := hinv) (y := arr[i - 1]) <;> try assumption
      . simp [ArrSet]
      . simp [ArrSet]
      . simp [ArrSet]
      . rw [List.pairwise_iff_getElem] at hsorted
        cases Nat.lt_or_ge j (i - 1) with
        | inl hj_lt =>
          have hlt : YjsLt' (A := A) (YjsPtr.itemPtr arr[j]) (YjsPtr.itemPtr arr[i - 1]) := by
            apply hsorted; assumption
          obtain ⟨ k, hlt ⟩ := hlt
          simp at *
          apply Exists.intro (k + 1)
          apply YjsLeq.leqLt
          assumption
          intros
          simp; omega
        | inr hj_ge =>
          have heq : j = i - 1 := by omega
          subst heq
          simp
          exists 0
          apply YjsLeq.leqSame
      . apply hlt1; omega
    . intros j hij hjlen
      simp at hjlen
      apply yjs_leq'_p_trans2 (inv := hinv) (y := YjsPtr.itemPtr arr[i]) <;> try assumption
      . simp [ArrSet]
      . simp [ArrSet]
      . simp [ArrSet]
      . apply hlt2
      . rw [List.pairwise_iff_getElem] at hsorted
        cases Nat.lt_or_ge i j with
        | inl hj_lt =>
          have hlt : YjsLt' (A := A) (YjsPtr.itemPtr arr[i]) (YjsPtr.itemPtr arr[j]) := by
            apply hsorted; try assumption
          obtain ⟨ h, hlt' ⟩ := hlt
          exists h + 1; right; assumption
        | inr hj_ge =>
          have heq : j = i := by omega
          subst heq
          simp
          exists 0; apply YjsLeq.leqSame
  . rw [List.insertIdxIfInBounds_toArray]
    apply List.Pairwise_insertIdx <;> try assumption
    . intros
      apply hneq
      simp
    . intros j hij hlt heq
      apply hneq arr[j]
      simp
      rw [heq]; simp

/-- `SortedInsertPos` form of `YjsArrInvariant_insertIdxIfInBounds`. -/
theorem SortedInsertPos.insertIdxIfInBounds_inv {arr : Array (YjsItem A)} {u : YjsItem A}
    {leftIdx rightIdx : ℤ} {d : ℕ} (ctx : IntegrateCtx arr u leftIdx rightIdx)
    (hpos : SortedInsertPos arr u d) :
    YjsArrInvariant (arr.insertIdxIfInBounds d u).toList := by
  apply YjsArrInvariant_insertIdxIfInBounds arr u d ctx.closed ctx.setInv ctx.arrInv hpos.le_size
  · intro h0
    exact hpos.before_lt (d - 1) (by omega) (by have := hpos.le_size; omega)
  · exact hpos.lt_after
  · intros a hmem heq
    rw [Array.mem_iff_getElem] at hmem
    obtain ⟨ k, hk, rfl ⟩ := hmem
    exact ctx.id_ne hk heq

/-! ## Main theorems -/

theorem YjsArrInvariant_integrate (input : IntegrateInput A) (arr newArr : Array (YjsItem A)) :
  YjsArrInvariant arr.toList
  → input.toItem arr = Except.ok newItem
  → newItem.isValid
  → maximalId newItem arr
  → integrate input arr = Except.ok newArr
  → ∃ i ≤ arr.size, newArr = arr.insertIdxIfInBounds i newItem ∧ YjsArrInvariant newArr.toList := by
  intros harrinv h_newItem_def h_valid h_maximalId hintegrate
  obtain ⟨ horigin_consistent, hreachable_consistent ⟩ := h_valid
  -- Unpack the `do` block of `integrate`.
  unfold integrate at hintegrate
  obtain ⟨ leftIdx, heqleft, hintegrate ⟩ := Except.bind_eq_ok_iff.1 hintegrate
  obtain ⟨ rightIdx, heqright, hintegrate ⟩ := Except.bind_eq_ok_iff.1 hintegrate
  obtain ⟨ destIdx, h_findInt, hintegrate ⟩ := Except.bind_eq_ok_iff.1 hintegrate
  obtain ⟨ item, h_item, hintegrate ⟩ := Except.bind_eq_ok_iff.1 hintegrate
  have h_newArr : newArr = arr.insertIdxIfInBounds destIdx item := by
    simpa [pure, Except.pure] using hintegrate.symm
  -- The item built by index lookup is `newItem`.
  have h_item_eq : item = newItem := by
    rw [IntegrateInput.toItem_ok_iff _ _ _ harrinv.unique] at h_newItem_def
    obtain ⟨ origin, rightOrigin, id, content, h_eq, horigin, hrightOrigin, hid, hcontent ⟩ := h_newItem_def
    obtain ⟨ originPtr, horiginptr, hleftIdPtr ⟩ := findLeftIdx_getElemExcept heqleft
    obtain ⟨ rightOriginPtr, hrightoriginptr, hrightIdPtr ⟩ := findRightIdx_getElemExcept heqright
    simp only [mkItemByIndex, horiginptr, hrightoriginptr, Except.ok_bind, pure, Except.pure] at h_item
    have h := isLeftIdPtr_unique _ _ _ _ harrinv.unique hleftIdPtr horigin
    have h' := isRightIdPtr_unique _ _ _ _ harrinv.unique hrightIdPtr hrightOrigin
    cases h_item
    subst h h' hid hcontent
    exact h_eq.symm
  subst h_item_eq
  -- The integration context.
  have heqleft' : findPtrIdx item.origin arr = Except.ok leftIdx := by
    rw [<-findLeftIdx_findPtrIdx_eq harrinv.unique h_newItem_def]; assumption
  have heqright' : findPtrIdx item.rightOrigin arr = Except.ok rightIdx := by
    rw [<-findRightIdx_findPtrIdx_eq harrinv.unique h_newItem_def]; assumption
  have horigin : ArrSet arr.toList item.origin := findPtrIdx_ArrSet heqleft'
  have hrorigin : ArrSet arr.toList item.rightOrigin := findPtrIdx_ArrSet heqright'
  have hclosed : IsClosedItemSet (ArrSet (item :: arr.toList)) :=
    arr_set_closed_push _ _ harrinv.closed horigin hrorigin
  have harrsetinv : ItemSetInvariant (ArrSet (item :: arr.toList)) := by
    apply item_set_invariant_push _ _ harrinv.item_set_inv harrinv.closed horigin_consistent
      hreachable_consistent
    intros x hmem heq
    have h := h_maximalId x hmem (by rw [heq])
    rw [heq] at h
    simp at h
  have ctx : IntegrateCtx arr item leftIdx rightIdx :=
    ⟨ harrinv, hclosed, harrsetinv, h_maximalId, heqleft', heqright' ⟩
  -- The loop returned the sorted insertion position.
  have hpos : SortedInsertPos arr item destIdx := by
    have hP : (match findIntegratedIndex leftIdx rightIdx input arr with
        | Except.ok d => SortedInsertPos arr item d
        | Except.error _ => True) := by
      apply Except.of_wp (prog := findIntegratedIndex leftIdx rightIdx input arr)
        (P := fun r => match r with
          | Except.ok d => SortedInsertPos arr item d
          | Except.error _ => True)
      exact fun _ => findIntegratedIndex_spec input ctx h_newItem_def trivial
    simpa [h_findInt] using hP
  exact ⟨ destIdx, hpos.le_size, h_newArr, h_newArr ▸ hpos.insertIdxIfInBounds_inv ctx ⟩

omit [DecidableEq A] in theorem isClockSafe_maximalId {arr : Array (YjsItem A)} {input : IntegrateInput A} {newItem : YjsItem A} :
  uniqueId arr.toList →
  input.toItem arr = Except.ok newItem →
  (maximalId newItem arr ↔ isClockSafe input.id arr) := by
  intros h_arr_uniqueId h_newItem_def
  rw [IntegrateInput.toItem_ok_iff _ _ _ h_arr_uniqueId] at h_newItem_def
  constructor
  . intros h_UniqueId
    simp [isClockSafe]
    intros x h_x
    replace h_UniqueId := h_UniqueId arr[x] (by simp [ArrSet])
    grind only
  . intros hisClockSafe
    simp [isClockSafe] at hisClockSafe
    intros x hmem heq
    simp [ArrSet] at hmem
    rw [Array.mem_iff_getElem] at hmem
    obtain ⟨ i, _, heq_getElem ⟩ := hmem
    grind only

theorem YjsArrInvariant_integrateSafe (input : IntegrateInput A) (newItem : YjsItem A) (arr newArr : Array (YjsItem A)) :
  YjsArrInvariant arr.toList
  → input.toItem arr = Except.ok newItem
  → newItem.isValid
  -> integrateSafe input arr = Except.ok newArr
  -> ∃ i ≤ arr.size, newArr = arr.insertIdxIfInBounds i newItem ∧ YjsArrInvariant newArr.toList := by
  intros harrinv h_newItem_def h_valid hintegrate
  simp [integrateSafe] at hintegrate
  split at hintegrate
  . rw [<-isClockSafe_maximalId harrinv.unique h_newItem_def] at *
    apply YjsArrInvariant_integrate input arr newArr harrinv h_newItem_def h_valid (by assumption) hintegrate
  . cases hintegrate

theorem YjsStateInvariant_insert (arr newArr : YjsState A) (input : IntegrateInput A) :
  YjsStateInvariant arr
  → input.toItem arr.items = Except.ok newItem
  → newItem.isValid
  → arr.insert input = Except.ok newArr
  → YjsStateInvariant newArr := by
  intros hstateinv h_newItem_def h_valid h_insert
  simp [YjsStateInvariant, YjsState.insert] at *
  generalize heq : integrateSafe input arr.items = result at h_insert
  obtain ⟨ _ ⟩ | ⟨ result ⟩ := result; cases h_insert
  simp at *
  grind [YjsArrInvariant_integrateSafe]

import LeanYjs.Algorithm.Insert.Basic

variable {A : Type} [DecidableEq A]

theorem findPtrIdx_item_exists (arr : Array (YjsItem A)) (x : YjsItem A) :
  findPtrIdx x arr = Except.ok i ->
  ∃j, i.toNat? = some j ∧ arr[j]? = some x := by
  intros hfind
  simp [findPtrIdx] at hfind
  generalize heq : Array.findIdx? (fun i => i = x) arr = idx at hfind
  cases idx <;> cases hfind
  constructor; constructor
  . unfold Int.toNat?
    eq_refl
  . rw [Array.findIdx?_eq_some_iff_getElem] at heq
    obtain ⟨ h, h1, h2 ⟩ := heq
    rw [Array.getElem?_eq_getElem]
    rw [decide_eq_true_eq] at h1
    simp; assumption

theorem findPtrIdx_eq_ok_inj {arr : Array (YjsItem A)} (x y : YjsPtr A) :
  findPtrIdx x arr = Except.ok i →
  findPtrIdx y arr = Except.ok i →
   x = y := by
  intros heq_x heq_y
  cases x with
  | first =>
    cases y with
    | first =>
      simp
    | last =>
      simp [findPtrIdx] at heq_x heq_y
      cases heq_x
      cases heq_y
    | itemPtr y =>
      exfalso
      simp [findPtrIdx] at heq_x heq_y
      generalize heq :  Array.findIdx? (fun i => decide (i = y)) arr = idx at *
      cases idx <;> cases heq_y
      cases heq_x
  | last =>
    cases y with
    | first =>
      simp [findPtrIdx] at heq_x heq_y
      cases heq_x
      cases heq_y
    | last =>
      simp
    | itemPtr y =>
      exfalso
      simp [findPtrIdx] at heq_x heq_y
      generalize heq :  Array.findIdx? (fun i => decide (i = y)) arr = idx at *
      cases idx <;> cases heq_y
      cases heq_x
      rw [Array.findIdx?_eq_some_iff_findIdx_eq] at heq
      omega
  | itemPtr x =>
    cases y with
    | first =>
      exfalso
      simp [findPtrIdx] at heq_x heq_y
      generalize heq :  Array.findIdx? (fun i => decide (i = x)) arr = idx at *
      cases idx <;> cases heq_x
      cases heq_y
    | last =>
      exfalso
      simp [findPtrIdx] at heq_x heq_y
      generalize heq :  Array.findIdx? (fun i => decide (i = x)) arr = idx at *
      cases idx <;> cases heq_x
      cases heq_y
      rw [Array.findIdx?_eq_some_iff_findIdx_eq] at heq
      omega
    | itemPtr y =>
      simp [findPtrIdx] at heq_x heq_y
      generalize heq_x :  Array.findIdx? (fun i => decide (i = x)) arr = idxX at *
      generalize heq_y :  Array.findIdx? (fun i => decide (i = y)) arr = idxY at *
      cases idxX <;> cases heq_x
      cases idxY <;> cases heq_y
      rw [Array.findIdx?_eq_some_iff_findIdx_eq] at heq_x
      rw [Array.findIdx?_eq_some_iff_findIdx_eq] at heq_y
      obtain ⟨ hlt_x, heq_x ⟩ := heq_x
      obtain ⟨ hlt_y, heq_y ⟩ := heq_y
      rw [Array.findIdx_eq hlt_x] at heq_x
      rw [Array.findIdx_eq hlt_y] at heq_y
      simp at heq_x heq_y
      obtain ⟨ heq_x, _ ⟩ := heq_x
      obtain ⟨ heq_y, _ ⟩ := heq_y
      subst x y
      simp

theorem findPtrIdx_ge_minus_1 {arr : Array (YjsItem A)} (item : YjsPtr A) :
  findPtrIdx item arr = Except.ok idx
  -> idx ≥ -1 := by
  intros hfind
  unfold findPtrIdx at hfind
  cases item with
  | first =>
    simp at hfind
    cases hfind
    simp
  | last =>
    simp at hfind
    cases hfind
    omega
  | itemPtr item =>
    simp at hfind
    generalize heq : Array.findIdx? (fun i => decide (i = item)) arr = idx at hfind
    cases idx with
    | none =>
      cases hfind
    | some idx =>
      cases hfind
      omega

theorem findPtrIdx_le_size {arr : Array (YjsItem A)} (item : YjsPtr A) :
  findPtrIdx item arr = Except.ok idx
  -> idx ≤ arr.size := by
  intros hfind
  unfold findPtrIdx at hfind
  cases item with
  | first =>
    simp at hfind
    cases hfind
    omega
  | last =>
    simp at hfind
    cases hfind
    simp
  | itemPtr item =>
    simp at hfind
    generalize heq : Array.findIdx? (fun i => decide (i = item)) arr = idx at hfind
    cases idx with
    | none =>
      cases hfind
    | some idx =>
      cases hfind
      rw [Array.findIdx?_eq_some_iff_findIdx_eq] at heq
      obtain ⟨ _, _ ⟩ := heq
      simp
      omega

/-! ### Bounds of the index lookups -/

omit [DecidableEq A] in
theorem findLeftIdx_bounds {originId : Option YjsId} {arr : Array (YjsItem A)} {idx : ℤ}
    (h : findLeftIdx originId arr = Except.ok idx) : -1 ≤ idx ∧ idx < arr.size := by
  cases originId with
  | none =>
    simp [findLeftIdx, pure, Except.pure] at h
    subst h
    constructor <;> omega
  | some id =>
    simp only [findLeftIdx] at h
    cases hf : arr.findIdx? (fun item => item.id = id) with
    | none => simp [hf] at h
    | some k =>
      simp [hf, pure, Except.pure] at h
      subst h
      have := (Array.findIdx?_eq_some_iff_getElem.1 hf).1
      constructor <;> omega

omit [DecidableEq A] in
theorem findRightIdx_bounds {rightOriginId : Option YjsId} {arr : Array (YjsItem A)} {idx : ℤ}
    (h : findRightIdx rightOriginId arr = Except.ok idx) : -1 ≤ idx ∧ idx ≤ arr.size := by
  cases rightOriginId with
  | none =>
    simp [findRightIdx, pure, Except.pure] at h
    subst h
    constructor <;> omega
  | some id =>
    simp only [findRightIdx] at h
    cases hf : arr.findIdx? (fun item => item.id = id) with
    | none => simp [hf] at h
    | some k =>
      simp [hf, pure, Except.pure] at h
      subst h
      have := (Array.findIdx?_eq_some_iff_getElem.1 hf).1
      constructor <;> omega

/-! ### What `toItem` depends on

`IntegrateInput.toItem` looks the array up only through `find?` on the two
dependency identifiers (`originId`, `rightOriginId`).  The lemmas below make this
explicit; they are the basis of the replay-determinism argument in
`LeanYjs.Network.Yjs.YjsNetwork`. -/

/-- The identifiers an insert input refers to: its origin and right origin, when present. -/
def IntegrateInput.depIds (input : IntegrateInput A) : List YjsId :=
  input.originId.toList ++ input.rightOriginId.toList

omit [DecidableEq A] in
theorem Array.find?_id_eq {arr : Array (YjsItem A)} {oid : YjsId} {x : YjsItem A}
    (h : arr.find? (fun i => i.id = oid) = some x) : x.id = oid := by
  simpa using Array.find?_some h

/-- The pointer that `originId` resolves to: `first` when absent, otherwise the item found by id. -/
@[simp] abbrev isLeftIdPtr (arr : Array (YjsItem A)) (id : Option YjsId) (ptr : YjsPtr A) : Prop :=
  match id with
  | none => ptr = YjsPtr.first
  | some pid =>
    ∃(item : YjsItem A), ptr = YjsPtr.itemPtr item ∧ arr.find? (fun i => i.id = pid) = some item

/-- The pointer that `rightOriginId` resolves to: `last` when absent, otherwise the item found by id. -/
@[simp] abbrev isRightIdPtr (arr : Array (YjsItem A)) (id : Option YjsId) (ptr : YjsPtr A) : Prop :=
  match id with
  | none => ptr = YjsPtr.last
  | some pid =>
    ∃(item : YjsItem A), ptr = YjsPtr.itemPtr item ∧ arr.find? (fun i => i.id = pid) = some item

omit [DecidableEq A] in
/-- Characterisation of a successful `toItem`: the item is built from the input's id and
content and from the two pointers its dependency ids resolve to. -/
theorem IntegrateInput.toItem_eq_ok_iff {input : IntegrateInput A} {arr : Array (YjsItem A)}
    {item : YjsItem A} :
    input.toItem arr = Except.ok item ↔
      ∃ o r, item = YjsItem.mk o r input.id input.content ∧
        isLeftIdPtr arr input.originId o ∧ isRightIdPtr arr input.rightOriginId r := by
  unfold IntegrateInput.toItem
  cases ho : input.originId with
  | none =>
    cases hr : input.rightOriginId with
    | none => simp [bind, Except.bind, pure, Except.pure]; exact eq_comm
    | some rid =>
      cases hf : arr.find? (fun i => i.id = rid) with
      | none => simp [hf, bind, Except.bind]
      | some x => simp [hf, bind, Except.bind, pure, Except.pure]; exact eq_comm
  | some oid =>
    cases hf : arr.find? (fun i => i.id = oid) with
    | none => simp [hf, bind, Except.bind]
    | some x =>
      cases hr : input.rightOriginId with
      | none => simp [hf, bind, Except.bind, pure, Except.pure]; exact eq_comm
      | some rid =>
        cases hf' : arr.find? (fun i => i.id = rid) with
        | none => simp [hf, hf', bind, Except.bind]
        | some y => simp [hf, hf', bind, Except.bind, pure, Except.pure]; exact eq_comm

omit [DecidableEq A] in
/-- `toItem` only inspects the array through `find?` on the dependency ids. -/
theorem IntegrateInput.toItem_congr {input : IntegrateInput A} {arr₁ arr₂ : Array (YjsItem A)}
    (h : ∀ oid ∈ input.depIds,
      arr₁.find? (fun i => i.id = oid) = arr₂.find? (fun i => i.id = oid)) :
    input.toItem arr₁ = input.toItem arr₂ := by
  simp only [IntegrateInput.depIds, List.mem_append, Option.mem_toList] at h
  unfold IntegrateInput.toItem
  cases ho : input.originId with
  | none =>
    cases hr : input.rightOriginId with
    | none => rfl
    | some rid => simp only [h rid (Or.inr hr)]
  | some oid =>
    cases hr : input.rightOriginId with
    | none => simp only [h oid (Or.inl ho)]
    | some rid => simp only [h oid (Or.inl ho), h rid (Or.inr hr)]

omit [DecidableEq A] in
/-- A successful `toItem` resolves every dependency id in the array. -/
theorem IntegrateInput.toItem_find?_dep {input : IntegrateInput A} {arr : Array (YjsItem A)}
    {item : YjsItem A} (h : input.toItem arr = Except.ok item) {oid : YjsId}
    (hoid : oid ∈ input.depIds) : ∃ x, arr.find? (fun i => i.id = oid) = some x := by
  simp only [IntegrateInput.depIds, List.mem_append, Option.mem_toList] at hoid
  obtain ⟨ o, r, -, ho, hr ⟩ := IntegrateInput.toItem_eq_ok_iff.1 h
  rcases hoid with hoid | hoid
  · rw [hoid] at ho
    obtain ⟨ x, -, hx ⟩ := ho
    exact ⟨ x, hx ⟩
  · rw [hoid] at hr
    obtain ⟨ x, -, hx ⟩ := hr
    exact ⟨ x, hx ⟩

omit [DecidableEq A] in
/-- The item produced by `toItem` carries the input's id. -/
theorem IntegrateInput.toItem_id_eq (input : IntegrateInput A) (arr : Array (YjsItem A))
    (item : YjsItem A) : input.toItem arr = Except.ok item → item.id = input.id := by
  intro h
  obtain ⟨ o, r, rfl, -, - ⟩ := IntegrateInput.toItem_eq_ok_iff.1 h
  rfl

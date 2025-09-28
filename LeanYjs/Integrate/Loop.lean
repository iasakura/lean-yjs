import LeanYjs.Item
import LeanYjs.ItemOrder
import LeanYjs.YjsArray
import LeanYjs.Integrate

variable {A : Type}
variable [DecidableEq A]

def offsetToIndex (leftIdx : ℤ) (rightIdx : ℤ) (offset : Option ℕ) (isBreak : Bool) : ℕ :=
  let back := if isBreak then 1 else 0
  match offset with
  | none => rightIdx.toNat - back
  | some o => (leftIdx + o).toNat - back

def isBreak (state : ForInStep (MProd ℤ Bool)) : Bool :=
  match state with
  | ForInStep.done _ => true
  | ForInStep.yield _ => false

def isDone (state : ForInStep (MProd ℤ Bool)) (x : Option ℕ) : Bool :=
  (match x with
  | none => true
  | some _ => false) ||
  match state with
  | ForInStep.done _ => true
  | ForInStep.yield _ => false

def extGetElemExcept (arr : Array (YjsItem A)) (idx : Int) : Except IntegrateError (YjsPtr A) :=
  if idx = -1 then
    Except.ok YjsPtr.first
  else if idx = arr.size then
    Except.ok YjsPtr.last
  else
    if idx < 0 || idx >= arr.size then
      Except.error IntegrateError.notFound
    else
      match arr[idx.toNat]? with
      | some item => return item
      | none => Except.error IntegrateError.notFound

def loopInv (arr : Array (YjsItem A)) (newItem : YjsItem A) (leftIdx : ℤ) (rightIdx : ℤ)
    (x : Option ℕ) (state : ForInStep (MProd ℤ Bool)) :=
  -- when x is none, we are done so current is rightIdx
  -- when break from loop, current goes back by 1
  let current := offsetToIndex leftIdx rightIdx x (isBreak state)
  let ⟨ dest, scanning ⟩ := state.value
  let done := isDone state x
  (match x with
    | none => True
    | some x => 0 < x ∧ x < rightIdx - leftIdx) ∧
  (dest ≤ current) ∧
  (!scanning → !done -> dest = current) ∧
  let dest := dest.toNat;
  (∀ i : ℕ, i < dest -> (h_i_lt : i < arr.size) -> YjsLt' (A := A) arr[i] newItem) ∧
  (∀ i, (h_dest_i : dest ≤ i) -> (h_i_c : i < current) ->
    ∃ (i_lt_size : i < arr.size) (h_dest_lt : dest < arr.size),
      (arr[i].origin = newItem.origin ∧ newItem.id < arr[i].id ∨
        YjsLeq' (A := A) arr[dest] arr[i].origin)) ∧
  (scanning -> ∃ h_dest_lt : dest < arr.size, arr[dest].origin = newItem.origin) ∧
  (done -> ∀ item : YjsPtr A, extGetElemExcept arr current = Except.ok item -> YjsLt' (A := A) newItem item)

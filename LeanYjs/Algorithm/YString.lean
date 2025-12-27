import LeanYjs.Item
import LeanYjs.ClientId
import LeanYjs.Algorithm.Basic
import LeanYjs.Algorithm.Insert.Basic
import LeanYjs.Algorithm.Delete.Basic

abbrev Item := YjsItem Char
structure YString : Type where
  contents : Array Item

def YString.new : YString := { contents := #[] }

def extGetElemExcept (arr : Array (YjsItem A)) (idx : Int) : Except IntegrateError (YjsPtr A) :=
  if idx = -1 then
    Except.ok YjsPtr.first
  else if idx = arr.size then
    Except.ok YjsPtr.last
  else
    if idx < 0 || idx >= arr.size then
      Except.error IntegrateError.error
    else
      match arr[idx.toNat]? with
      | some item => return item
      | none => Except.error IntegrateError.error

def nextId (currentId : YjsId) : YjsId :=
  YjsId.mk currentId.clientId (currentId.clock + 1)

def YString.insert (s : YString) (i : Nat) (c : Char) : StateT YjsId (Except IntegrateError) YString := do
  if i > s.contents.size then
    throw $ IntegrateError.error
  let arr : Array Item := s.contents
  let origin <- extGetElemExcept arr (Int.ofNat i - 1)
  let rightOrigin <- extGetElemExcept arr (Int.ofNat i)
  let id := nextId (← StateT.get)
  let newItem : Item := YjsItem.mk origin rightOrigin id c false
  let arr <- integrate newItem s.contents
  pure { contents := arr }

def YString.delete (s : YString) (i : Nat) : Except IntegrateError YString :=
  if i >= s.contents.size then
    Except.error IntegrateError.error
  else
    let arr := s.contents
    match arr[i]? with
    | some item => do
      let newArr := deleteById s.contents item.id
      Except.ok { contents := newArr }
    | none => Except.error IntegrateError.error

def YString.toString (s : YString) : String :=
  String.ofList $ (s.contents.map (fun item => item.content)).toList

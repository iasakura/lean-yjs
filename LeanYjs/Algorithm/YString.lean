import LeanYjs.Item
import LeanYjs.ClientId
import LeanYjs.Algorithm.Basic
import LeanYjs.Algorithm.Insert.Basic
import LeanYjs.Algorithm.Delete.Basic

abbrev Item := YjsItem Char
structure YString : Type where
  contents : Array Item

def YString.new : YString := { contents := #[] }

def nextId (currentId : YjsId) : YjsId :=
  YjsId.mk currentId.clientId (currentId.clock + 1)

def ptrToId (p : YjsPtr Char) : Option YjsId :=
  match p with
  | YjsPtr.itemPtr item => some item.id
  | YjsPtr.first => none
  | YjsPtr.last => none

def YString.insert (s : YString) (i : Nat) (c : Char) : StateT YjsId (Except IntegrateError) YString := do
  if i > s.contents.size then
    throw $ IntegrateError.error
  let arr : Array Item := s.contents
  let origin <- getPtrExcept arr (Int.ofNat i - 1)
  let rightOrigin <- getPtrExcept arr (Int.ofNat i)
  let currentId <- StateT.get
  let id := nextId currentId
  StateT.set id
  let input : IntegrateInput Char := {
    originId := ptrToId origin
    rightOriginId := ptrToId rightOrigin
    content := c
    id := id
  }
  let arr <- integrate input s.contents
  pure { contents := arr }

def YString.delete (s : YString) (i : Nat) : Except IntegrateError YString :=
  if hlt : i < s.contents.size then
    Except.ok { contents := s.contents.eraseIdx i hlt }
  else
    Except.error IntegrateError.error

def YString.toString (s : YString) : String :=
  String.ofList $ (s.contents.map (fun item => item.content)).toList

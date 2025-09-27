import LeanYjs.Item
import LeanYjs.ClientId
import LeanYjs.Integrate

def Item := YjsItem Char
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
      Except.error IntegrateError.notFound
    else
      match arr[idx.toNat]? with
      | some item => return item
      | none => Except.error IntegrateError.notFound

def YString.insert (s : YString) (i : Nat) (c : Char) : ReaderT ClientId (Except IntegrateError) YString := do
  if i > s.contents.size then
    throw $ IntegrateError.outOfBounds i s.contents.size
  let arr : Array Item := s.contents
  let origin <- extGetElemExcept arr (Int.ofNat i - 1)
  let rightOrigin <- extGetElemExcept arr (Int.ofNat i)
  let clientId <- ReaderT.read
  let newItem : Item := YjsItem.item origin rightOrigin clientId c
  let arr <- integrate newItem s.contents
  pure { contents := arr }

def YString.toString (s : YString) : String :=
  String.mk $ (s.contents.map (fun item => item.content)).toList

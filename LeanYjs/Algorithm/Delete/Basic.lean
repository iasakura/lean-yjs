import LeanYjs.Item
import LeanYjs.Algorithm.Invariant.Basic
import LeanYjs.Algorithm.Invariant.YjsArray

mutual
def deleteItemById (item : YjsItem A) (id : YjsId) : YjsItem A :=
  match item with
  | YjsItem.mk o r iid c d =>
    if iid = id then
      YjsItem.mk (deletePtrById o id) (deletePtrById r id) iid c true
    else
      YjsItem.mk (deletePtrById o id) (deletePtrById r id) iid c d

def deletePtrById (ptr : YjsPtr A) (id : YjsId) : YjsPtr A :=
  match ptr with
  | YjsPtr.itemPtr item => YjsPtr.itemPtr (deleteItemById item id)
  | YjsPtr.first => YjsPtr.first
  | YjsPtr.last => YjsPtr.last
end

/--
  Delete the item with the given id from the array by marking it as deleted.
  Not only the item itself but also all its origins and right origins are marked as deleted.
  This is done to maintain the invariants of the Yjs array.
  In real Yjs implementation, it just change the field and does not traverse the origins because the origin/rightOrigins are references to other items.
-/
def deleteById (arr : Array (YjsItem A)) (id : YjsId) : Array (YjsItem A) :=
  -- Mark the item with the given id as deleted
  arr.map fun item => deleteItemById item id

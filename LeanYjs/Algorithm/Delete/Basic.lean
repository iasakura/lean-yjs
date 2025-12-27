import LeanYjs.Item

def deleteById (arr : Array (YjsItem A)) (id : YjsId) : Array (YjsItem A) :=
  -- Mark the item with the given id as deleted
  arr.map (fun item =>
    if item.id = id then
      YjsItem.mk item.origin item.rightOrigin item.id item.content true
    else
      item)

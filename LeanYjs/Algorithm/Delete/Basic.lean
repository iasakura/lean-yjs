import LeanYjs.Item
import LeanYjs.Algorithm.Basic

def deleteById (state : YjsState A) (id : YjsId) : YjsState A :=
  { state with
      deletedIds := state.deletedIds.insert id
  }

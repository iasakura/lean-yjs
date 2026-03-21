import LeanYjs.Indirect.Algorithm.Basic

namespace Indirect

def deleteById (state : YjsState A) (id : YjsId) : YjsState A :=
  { state with
      deletedIds := state.deletedIds.insert id
  }

end Indirect

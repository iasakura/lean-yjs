import LeanYjs.Algorithm.Commutativity.InsertInsert
import LeanYjs.Algorithm.Insert.SpecBridgeV2

variable {A : Type}
variable [DecidableEq A]

theorem integrate_commutative_of_v2
    (a b : IntegrateInput A) (aItem bItem : YjsItem A) (arr1 : Array (YjsItem A)) :
    YjsArrInvariant arr1.toList ->
    a.toItem arr1 = Except.ok aItem ->
    b.toItem arr1 = Except.ok bItem ->
    a.id.clientId ≠ b.id.clientId ->
    ¬ OriginReachableFromV2 (ItemSetV2.ofOldItems arr1.toList) aItem.toV2 bItem.toV2.toRef ->
    ¬ OriginReachableFromV2 (ItemSetV2.ofOldItems arr1.toList) bItem.toV2 aItem.toV2.toRef ->
    IsItemValidV2Against (ItemSetV2.ofOldItems arr1.toList) aItem ->
    IsItemValidV2Against (ItemSetV2.ofOldItems arr1.toList) bItem ->
    (do
      let arr2 <- integrateSafe a arr1
      integrateSafe b arr2) =
    (do
      let arr2' <- integrateSafe b arr1
      integrateSafe a arr2') := by
  intro hArr hAToItem hBToItem hClient hNotAB hNotBA hAValidV2 hBValidV2
  have hNotABOld : ¬ OriginReachable aItem (YjsPtr.itemPtr bItem) := by
    exact not_originReachable_of_not_fromV2AgainstOldItems hArr hAToItem hNotAB
  have hNotBAOld : ¬ OriginReachable bItem (YjsPtr.itemPtr aItem) := by
    exact not_originReachable_of_not_fromV2AgainstOldItems hArr hBToItem hNotBA
  have hAValid : aItem.isValid := by
    exact YjsItem.isValid_of_v2AgainstOldItems hArr hAToItem hAValidV2
  have hBValid : bItem.isValid := by
    exact YjsItem.isValid_of_v2AgainstOldItems hArr hBToItem hBValidV2
  exact integrate_commutative a b aItem bItem arr1
    hArr hAToItem hBToItem hClient hNotABOld hNotBAOld hAValid hBValid

theorem insert_commutative_of_v2
    (a b : IntegrateInput A) (aItem bItem : YjsItem A) (arr res : YjsState A) :
    YjsStateInvariant arr ->
    a.toItem arr.items = Except.ok aItem ->
    b.toItem arr.items = Except.ok bItem ->
    a.id.clientId ≠ b.id.clientId ->
    ¬ OriginReachableFromV2 (ItemSetV2.ofOldItems arr.items.toList) aItem.toV2 bItem.toV2.toRef ->
    ¬ OriginReachableFromV2 (ItemSetV2.ofOldItems arr.items.toList) bItem.toV2 aItem.toV2.toRef ->
    IsItemValidV2Against (ItemSetV2.ofOldItems arr.items.toList) aItem ->
    IsItemValidV2Against (ItemSetV2.ofOldItems arr.items.toList) bItem ->
    (do
      let arr2 <- arr.insert a
      arr2.insert b) = Except.ok res ->
    (do
      let arr2' <- arr.insert b
      arr2'.insert a) = Except.ok res := by
  intro hState hAToItem hBToItem hClient hNotAB hNotBA hAValidV2 hBValidV2 hEq
  have hNotABOld : ¬ OriginReachable aItem (YjsPtr.itemPtr bItem) := by
    exact not_originReachable_of_not_fromV2AgainstOldItems hState hAToItem hNotAB
  have hNotBAOld : ¬ OriginReachable bItem (YjsPtr.itemPtr aItem) := by
    exact not_originReachable_of_not_fromV2AgainstOldItems hState hBToItem hNotBA
  have hAValid : aItem.isValid := by
    exact YjsItem.isValid_of_v2AgainstOldItems hState hAToItem hAValidV2
  have hBValid : bItem.isValid := by
    exact YjsItem.isValid_of_v2AgainstOldItems hState hBToItem hBValidV2
  exact insert_commutative a b aItem bItem arr res
    hState hAToItem hBToItem hClient hNotABOld hNotBAOld hAValid hBValid hEq

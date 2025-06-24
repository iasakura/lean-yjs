import LeanYjs.Item
import LeanYjs.ActorId
import LeanYjs.ItemOriginOrder
import LeanYjs.ItemOrder

inductive IntegrateError where
| notFound : IntegrateError

variable {A: Type} [BEq A]

def findIdx (p : YjsPtr A) (arr : Array (YjsItem A)) : Except IntegrateError Int :=
  match p with
  | YjsPtr.itemPtr item =>
    match Array.findIdx? (fun i => i == item) arr with
    | some idx => return idx
    | none => Except.error IntegrateError.notFound
  | YjsPtr.first => return 0
  | YjsPtr.last => return (Array.size arr - 1)

def getExcept (arr : Array (YjsItem A)) (idx : Nat) : Except IntegrateError (YjsItem A) :=
  match arr[idx]? with
  | some item => return item
  | none => Except.error IntegrateError.notFound

def integrate (newItem : YjsItem A) (arr : Array (YjsItem A)) : Except IntegrateError (Array (YjsItem A)) := do
  let leftIdx <- findIdx (YjsItem.origin newItem) arr
  let rightIdx <- findIdx (YjsItem.rightOrigin newItem) arr
  let leftIdx := Int.toNat leftIdx
  let rightIdx := Int.toNat rightIdx

  let mut scanning := false
  let mut destIdx := leftIdx + 1
  for i in [leftIdx+1:rightIdx] do
    let other <- getExcept arr i

    if !scanning then
      destIdx := i

    let oLeftIdx <- findIdx other.origin arr
    let oRightIdx <- findIdx other.rightOrigin arr

    if oLeftIdx < leftIdx then
      break
    else if oLeftIdx == leftIdx then
      if newItem.id > other.id then
        scanning := false
        continue
      else if oRightIdx == rightIdx then
        break
      else
        scanning := true
        continue
    else
      continue

  return (Array.insertIdxIfInBounds arr (Int.toNat destIdx) newItem)

-- 再帰部分を分離した補助関数
def integrateRecursionAux (newItem : YjsItem A) (arr : Array (YjsItem A))
                          (leftIdx rightIdx : Nat) (i : Nat) (scanning : Bool)
                          : Except IntegrateError (Nat × Bool) := do
  -- ベースケース: 終了条件
  if i >= rightIdx then
    return (i, scanning)
  else
    -- 現在の項目を取得
    let other <- getExcept arr i
    -- 比較に必要なインデックスを取得
    let oLeftIdx <- findIdx other.origin arr
    let oRightIdx <- findIdx other.rightOrigin arr
    let oLeftIdx := Int.toNat oLeftIdx

    -- 条件チェックと再帰呼び出し
    if oLeftIdx < leftIdx then
      -- 挿入位置が見つかった
      return (i, true)
    else if oLeftIdx == leftIdx then
      if newItem.id > other.id then
        -- 次の項目へ進む、scanningをリセット
        integrateRecursionAux newItem arr leftIdx rightIdx (i+1) false
      else if oRightIdx == rightIdx then
        -- 挿入位置が決定
        return (i, false)
      else
        -- 次の項目へ進む、scanning = true
        integrateRecursionAux newItem arr leftIdx rightIdx (i+1) true
    else
      -- 次の項目へ進む、scanningは変更しない
      integrateRecursionAux newItem arr leftIdx rightIdx (i+1) scanning
  termination_by rightIdx - i

-- メイン関数
def integrateRecursion (newItem : YjsItem A) (arr : Array (YjsItem A)) : Except IntegrateError (Array (YjsItem A)) := do
  -- 必要なインデックスを取得
  let leftIdx <- findIdx (YjsItem.origin newItem) arr
  let rightIdx <- findIdx (YjsItem.rightOrigin newItem) arr
  let leftIdx := Int.toNat leftIdx
  let rightIdx := Int.toNat rightIdx

  -- 初期値で補助関数を呼び出し
  let (destIdx, _) <- integrateRecursionAux newItem arr leftIdx rightIdx (leftIdx + 1) false

  -- 結果の配列を返す
  return (Array.insertIdxIfInBounds arr destIdx newItem)

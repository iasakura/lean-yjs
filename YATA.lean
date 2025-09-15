import LeanYjs.Item
import LeanYjs.ClientId

-- YATAのintegrate algorithm実装
-- 擬似コードに基づく実装（YjsItemを直接使用）

variable {A: Type} [DecidableEq A]

-- エラー型の定義
inductive YATAIntegrateError where
| originNotFound : YATAIntegrateError
| invalidArrayAccess : YATAIntegrateError
| insertionFailed : YATAIntegrateError
deriving Repr, DecidableEq

-- 配列内でYjsPtrのインデックスを検索する関数
def findPtrIdx (ptr : YjsPtr A) (items : Array (YjsItem A)) : Except YATAIntegrateError Int :=
  match ptr with
  | YjsPtr.itemPtr targetItem =>
    match Array.findIdx? (fun item => item = targetItem) items with
    | some idx => return idx
    | none => Except.error YATAIntegrateError.originNotFound
  | YjsPtr.first => return -1
  | YjsPtr.last => return items.size

-- originの比較（配列内のインデックスベース）
def compareOriginByIdx (a b : YjsPtr A) (items : Array (YjsItem A)) : Except YATAIntegrateError Bool := do
  let aIdx <- findPtrIdx a items
  let bIdx <- findPtrIdx b items
  return aIdx < bIdx

def originEqualByIdx (a b : YjsPtr A) (items : Array (YjsItem A)) : Except YATAIntegrateError Bool := do
  let aIdx <- findPtrIdx a items
  let bIdx <- findPtrIdx b items
  return aIdx = bIdx

def originLessEqualByIdx (a b : YjsPtr A) (items : Array (YjsItem A)) : Except YATAIntegrateError Bool := do
  let equal <- originEqualByIdx a b items
  if equal then
    return true
  else
    compareOriginByIdx a b items

def originGreaterByIdx (a b : YjsPtr A) (items : Array (YjsItem A)) : Except YATAIntegrateError Bool := do
  let lessEqual <- originLessEqualByIdx a b items
  return not lessEqual

-- YjsItemの比較（creator/actor IDベース）
def compareYjsItems (a b : YjsItem A) : Bool :=
  match a, b with
  | YjsItem.item _ _ creatorA _, YjsItem.item _ _ creatorB _ => creatorA < creatorB

-- YATAのintegrate algorithm
-- Insert 'newItem' in a list of items
-- 画像の擬似コードに基づく実装
def yataIntegrateItem (newItem : YjsItem A) (items : Array (YjsItem A)) :
  Except YATAIntegrateError (Array (YjsItem A)) := do
  if items.size = 0 then
    return #[newItem]
  else
    let mut result := items
    let mut insertPos := 0

    -- 新しいアイテムの origin を取得
    let newOrigin := newItem.origin

    -- Rule 2: Search for the last operation that is to the left of newItem
    for h : idx in [:items.size] do
      let currentItem := items[idx]'(by simp [h.2])
      let currentOrigin := currentItem.origin

      -- YATAのルールに基づく比較
      -- if (currentItem < newOrigin OR newOrigin <= currentOrigin)
      -- AND (currentOrigin != newOrigin OR currentItem.creator < newItem.creator) do
      let cond1 <- compareOriginByIdx currentOrigin newOrigin items
      let cond2 <- originLessEqualByIdx newOrigin currentOrigin items
      let cond3 <- originEqualByIdx currentOrigin newOrigin items

      if (cond1 || cond2) && (not cond3 || compareYjsItems currentItem newItem) then
        -- rule 1 and 3: この条件が満たされる場合、newItemはcurrentItemの後継
        insertPos := idx + 1
      else
        -- Breaking condition: Rule 1が満たされなくなった場合
        let shouldBreak <- originGreaterByIdx newOrigin currentOrigin items
        if shouldBreak then
          -- Rule 1 is no longer satisfied since otherwise origin connections would cross
          break

    -- 配列に挿入
    if insertPos <= items.size then
      return Array.insertIdx! result insertPos newItem
    else
      Except.error YATAIntegrateError.insertionFailed

-- リスト形式での実装
def yataIntegrateList (newItem : YjsItem A) (items : List (YjsItem A)) :
  Except YATAIntegrateError (List (YjsItem A)) := do
  let itemArray := items.toArray
  let resultArray <- yataIntegrateItem newItem itemArray
  return resultArray.toList

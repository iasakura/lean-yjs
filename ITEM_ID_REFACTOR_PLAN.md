# Item ID Refactor Plan

## Goal

`YjsItem` が `origin` / `rightOrigin` として別の `YjsItem` そのものを保持している現状をやめ、参照先は `id` ベースで表現する。

この変更の主目的は次の 2 点。

- データ表現を非再帰化して、状態・操作・永続化の境界を明確にする
- order / validity / convergence の証明が、特定の自己埋め込み構造ではなく、明示的な `ItemSet` 仮定の上で動くようにする

この文書は、実装前の詳細な移行計画と、どこが重くなるかの見積もりを残すためのもの。

## Summary

結論だけ先に書くと、この変更は「`Item` の field を差し替える」作業ではなく、「order 証明基盤を `ItemSet` 依存に載せ替える」作業である。

影響の大きさは次の順になる。

1. `LeanYjs/Order/*`
2. `LeanYjs/Algorithm/Insert/Spec.lean`
3. `LeanYjs/Algorithm/Commutativity/InsertInsert.lean`
4. `LeanYjs/Algorithm/Invariant/*`
5. `LeanYjs/Algorithm/Insert/Basic.lean`
6. `LeanYjs/Network/Yjs/YjsNetwork.lean`

実行コードだけを見ると軽く見えるが、証明の中心が現状の再帰的 `YjsPtr` / `YjsItem` に深く依存しているため、order 層とその利用箇所が工数の中心になる。

## Progress

現時点で、既存定義を壊さない v2 土台を追加済み。

- `LeanYjs/ItemV2.lean`
  - `ItemRef`
  - `YjsItemV2`
- `LeanYjs/ItemSetV2.lean`
  - `lookup` ベースの `ItemSetV2`
  - `ItemIn` / `RefIn`
  - `DependsOnId`
  - `WellFoundedItemSetV2.induction`
- `LeanYjs/Order/ItemOrderV2.lean`
  - `OriginReachableStepV2`
  - `OriginReachableV2`
  - `YjsLtV2` / `YjsLeqV2` / `ConflictLtV2` の skeleton
- `LeanYjs/Order/ItemSetInvariantV2.lean`
  - `origin_lt_rightOrigin`
  - `origin_nearest_reachable`
  - structural invariant からの補題
- `LeanYjs/Order/MeasureV2.lean`
  - `idDepth` / `refDepth`
  - dependency / reachability が depth を strictly 下げる補題
  - pair / triple recursion 用の measure helper
- `LeanYjs/Order/SizeV2.lean`
  - `idSize` / `refSize`
  - additive な `pairSize` / `tripleSize`
  - transitivity / asymmetry 用の帰納法基盤
- `LeanYjs/Order/TotalityV2.lean`
  - `YjsId_lt_total`
  - `first` / `last` の base ordering
  - pair / triple measure induction combinator
  - `yjsLeq_or_yjsLt`
- `LeanYjs/Order/BoundaryV2.lean`
  - `not_ref_lt_first`
  - `not_last_lt_ref`
  - sentinel impossibility を `TransitivityV2` / `AsymmetryV2` の共通土台に分離
- `LeanYjs/Order/TransitivityV2.lean`
  - `YjsId_lt_trans_v2`
  - conflict helper 群
  - `yjsLt_trans_v2`
  - `yjsLeq_lt_trans_v2`
  - `yjsLt_leq_trans_v2`
  - `yjsLeq_trans_v2`
- `LeanYjs/Order/AsymmetryV2.lean`
  - `yjsLt_conflictLt_decreases_v2`
  - `yjsLeq_rightOrigin_decreases_v2`
  - `yjsLeq_origin_decreases_v2`
  - `yjsLt_asymm_v2`
  - `yjsLt_of_not_leq_v2`

この進捗により、次の方針修正が確定した。

- `ItemSet` は `mem` を別に持つより、`lookup` を primitive にした方がよい
- reachability は `YjsItem -> ItemRef` より `ItemRef -> ItemRef` の transitive closure として持つ方が order に繋げやすい
- `id_unique` は invariant field に持つより、lookup から導出する方が自然
- order の endpoints は `ItemRef` で十分で、conflict の証拠だけ item を持つ形にすると constructor が素直
- `DependsOnId` は各 item につき高々 2 本の outgoing edge しかないので、`wfDependsOnId.fix` で `depth : YjsId -> Nat` を直接定義できる
- 同じく `wfDependsOnId.fix` で additive な `sizeV2 : YjsId -> Nat` も定義できる
- totality そのものは `origin_nearest_reachable` や `origin_lt_rightOrigin` にはまだ依存せず、structural `wf` と lookup uniqueness だけでかなり進められる
- 旧実装と同様に、full `Asymmetry` は `Transitivity` に依存する形が自然で、v2 でもその依存は残る
- そのため `first/last` 境界補題は `AsymmetryV2` に置かず、`BoundaryV2` として前段に分離する方が import graph が安定する
- transitivity / asymmetry は `depth` より `sizeV2` の方が旧証明と整合的
- 理由は `sizeV2 item = sizeV2 origin + sizeV2 rightOrigin + 1` という加算形が保たれるためで、middle item を両側へ展開する再帰枝で素直に measure が下がる
- したがって measure は用途別に分ける
  - totality: `depth`
  - transitivity / asymmetry: `sizeV2`
- order core (`totality` / `transitivity` / `asymmetry`) は v2 側で一通り揃った
- 次の重い作業は order 証明そのものではなく、`Invariant` / `Insert/Spec` / `InsertInsert` を v2 order に載せ替える段階に移った
- 移行は big-bang より staged bridge の方が安全
  - まず既存の recursive `YjsItem` / `YjsPtr` から `YjsItemV2` / `ItemSetV2` への変換層を置く
  - その上で既存 array/state を保ったまま v2 order を利用可能にする
  - 最後に storage / algorithm 本体を v2 表現へ置き換える
- `LeanYjs/Algorithm/Invariant/BridgeV2.lean` で old order / reachability から v2 order への semantic bridge を追加済み
  - `OriginReachableStep` / `OriginReachable`
  - `YjsLt'` / `YjsLeq'`
  - `origin_lt_rightOrigin`
  - `origin_nearest_reachable`
- `LeanYjs/Algorithm/Invariant/StructuralBridgeV2.lean` で old array から `ItemSetV2.ofOldItems` への structural bridge を追加済み
  - `ofOldItems_structural`
  - `origin_lt_rightOrigin_field_to_v2`
- reverse reachability bridge も `StructuralBridgeV2` で追加済み
  - `ptr_eq_of_toRefV2_eq`
  - `originReachableStep_from_v2`
  - `originReachable_from_v2`
- その結果、old array invariant から full `YjsItemSetInvariantV2` を構成する bridge まで完了した
  - `ofOldItems_invariant_v2`
- ここまでで、old recursive storage を維持したまま v2 order core を downstream proof に注入できる状態になった
- `LeanYjs/Algorithm/Invariant/YjsArrayBridgeV2.lean` で array/state 層の公開補題も追加済み
  - `YjsArrInvariant.uniqueIdOld`
  - `YjsArrInvariant.itemSetInvariantV2`
  - `YjsStateInvariant.itemSetInvariantV2`
  - `YjsArrInvariant.yjsLeq_or_yjsLtV2`
  - `YjsStateInvariant.yjsLeq_or_yjsLtV2`
  - `same_yjs_set_ofOldItems_eq`
- これで `Insert/Spec` や network proof は old `ItemSetInvariant` を直接剥がさなくても、`YjsArrInvariant` / `YjsStateInvariant` から v2 totality を引ける
- さらに `same_yjs_set_unique` が必要だった箇所では、old list equality を経由して `ItemSetV2.ofOldItems` の equality まで rewrite できる
- `LeanYjs/Algorithm/Insert/SpecBridgeV2.lean` で insert spec 境界の thin wrapper も追加済み
  - `YjsArrInvariant_integrate_itemSetInvariantV2`
  - `YjsArrInvariant_integrateSafe_itemSetInvariantV2`
  - `YjsStateInvariant_insert_itemSetInvariantV2`
  - `IsItemValidV2Against`
  - `YjsItem.isValid_toV2AgainstOldItems`
  - `YjsItem.isValid_of_v2AgainstOldItems`
  - `YjsItem.isValid_iff_v2AgainstOldItems`
- これで integration correctness を使う consumer は、既存 theorem を壊さずに `newArr` 側の v2 invariant を直接受け取れる
- さらに new item がまだ old item-set に入っていない段階でも、`item.isValid` を `ItemSetV2.ofOldItems arr` に対する v2 validity へ読み替えられる
- reverse bridge も入ったので、必要なら v2 validity から old `item.isValid` へ戻して既存 theorem に渡せる
- `LeanYjs/Algorithm/Insert/BasicV2.lean` で insert algorithm 側の v2-native entrypoint も追加済み
  - `IntegrateInput.toItemV2`
  - `getRefExcept`
  - `mkItemV2ByIndex`
  - `findRefIdx`
  - `findIntegratedIndexV2`
  - `integrateV2Item`
  - old algorithm との対応補題
    - `IntegrateInput.toItem_toItemV2`
    - `getPtrExcept_toRefExcept`
    - `mkItemByIndex_toV2`
  - bounds / id preservation の spec
    - `findRefIdx_spec`
    - `getRefExcept_spec`
    - `mkItemV2ByIndex_spec`
    - `findIntegratedIndexV2_ok_le_size`
    - `integrateV2Item_spec`
- これにより、まだ storage 自体は old recursive item のままでも、
  algorithm 境界では `YjsItemV2` / `ItemRef` を直接返す補助 API を使い始められる
- 特に insert scan の本体は `YjsPtr` の構造ではなく
  「ref を index に戻す」「other item の origin/rightOrigin を id-ref として読む」
  だけで動くことが確認できた
- したがって `Insert.Basic` の本体移行は、
  order 証明の全面移植を待たずに段階的に進められる
- `LeanYjs/Algorithm/Insert/BasicBridgeV2.lean` で scan loop に必要な局所 bridge も追加した
  - `findRefIdx_toRefV2_eq_findPtrIdx`
  - `findRefIdx_origin_eq_findPtrIdx`
  - `findRefIdx_rightOrigin_eq_findPtrIdx`
  - `getElemExcept_mem`
  - `getElemExcept_findRefIdx_origin_eq_findPtrIdx`
  - `getElemExcept_findRefIdx_rightOrigin_eq_findPtrIdx`
  - `getElemExcept_lookupPairV2_eq_lookupPair`
- ここまでで `other <- getElemExcept arr i` の地点では、old scan と v2 scan の lookup は完全に一致させられる
- さらに scan loop 自体も helper 化して old scan と一致するところまで進めた
  - `scanStepV2`
  - `scanStepOld`
  - `forIn_list_congr`
  - `scanStepV2_eq_scanStepOld`
  - `findIntegratedIndexV2_eq_findIntegratedIndex`
  - `integrateV2Item_eq_integrateScan`
- これで `findIntegratedIndexV2` は old scan と theorem-level に一致する
- `integrateV2Item` も old `findIntegratedIndex` を使う形へ bridge できたので、
  次は `mkItemByIndex_toV2` と合わせて old `integrate` / `integrateSafe` の postcondition を
  v2 item へ移す段階に入れる
- ただしここで方針を修正する:
  - bridge 拡張はこの `scan equivalence` を checkpoint にして止める
  - これ以上 old `integrate` / `integrateSafe` / `Spec` への還元 wrapper を厚くしない
  - 以後の主戦場は `Spec` の v2-native 直移植に切り替える
- 理由:
  - `findIntegratedIndexV2_eq_findIntegratedIndex` までで v2 scan の挙動確認としては十分
  - ここから先に old theorem への還元を増やしても、最終目標の
    「recursive `YjsItem` / `YjsPtr` 非依存」にはほとんど近づかない
  - 重い残課題は `loopInv` と scan 局所補題群の v2 化で、そこは bridge 完成とは独立に残る
- pivot 後の優先順位:
  1. `SpecV2` / `SpecPortV2` を新設する
  2. `scanStepV2` ベースの `loopInvV2` を定義する
  3. `loopInv_YjsLt'` など scan 局所補題を `findRefIdx` / `ItemRef` / `YjsLtV2` ベースへ移植する
  4. `YjsArrInvariant_integrate` 相当の v2-native theorem を、old theorem 非依存で立てる
  5. その後で storage を old recursive item から外す
- pivot の最初の checkpoint として `LeanYjs/Algorithm/Insert/SpecPortV2.lean` を追加した
  - `activeSetV2 := (ItemSetV2.ofOldItems arr.toList).withItem newItem`
  - `offsetToIndexV2` / `isBreakV2` / `isDoneV2`
  - `extGetElemExceptV2 := getRefExcept`
  - `loopInvV2` の最初の skeleton
  - `toItemV2_origin_refIn_oldItems`
  - `toItemV2_rightOrigin_refIn_oldItems`
  - `activeSetV2_closed`
  - `activeSetV2_closed_of_toItemV2`
- その次の checkpoint として index-based builder からも同じ active-set 閉包を取れるようにした
  - `getRefExcept_refIn_oldItems`
  - `mkItemV2ByIndex_origin_refIn_oldItems`
  - `mkItemV2ByIndex_rightOrigin_refIn_oldItems`
  - `activeSetV2_closed_of_mkItemV2ByIndex`
- これで `SpecPortV2` は
  - id-based input decode (`toItemV2`)
  - index-based local builder (`mkItemV2ByIndex`)
  の両方から proof-local active set の closedness を取り出せる
- さらに scan arithmetic の最初の移植として
  - `offsetToIndexV2_range'_getElem`
  を追加した
  - これは old `Spec` の `List.range'` ベースの loop body 補題を v2 側へ移すときの共通下敷きになる
- さらに `loopInvV2` の分解を直接使えるように、projection 補題を追加した
  - `loopInvV2_offset_bounds`
  - `loopInvV2_dest_le_current`
  - `loopInvV2_dest_eq_current_of_not_scanning`
  - `loopInvV2_lt_prefix`
  - `loopInvV2_scanning_origin`
  - `loopInvV2_done_lt`
  - これで preservation proof 側では毎回 `loopInvV2` を手展開せずに、必要な成分だけを呼び出せる
- 一方で `scanStepV2` の branch-shape を直接露出する補題は、この段階では保留にした
  - do-notation 展開に引きずられて証明が brittle になりやすい
  - 先に `loopInvV2` 側の projection と preservation を積み、必要になったら statement を絞って再導入する
- `withItem` を本格利用するための structural 補題も追加した
  - `ItemSetV2.dependsOnId_withItem_of_ne`
  - `ItemSetV2.wellFounded_withItem`
  - `SpecPortV2.activeSetV2_structural`
  - これで `activeSetV2` は `closed` だけでなく、fresh id 仮定つきで `WellFoundedItemSetV2` まで引ける
  - 次段ではここから `activeSetV2` 上の totality / transitivity を proof-local に使えるようにする
- ここで `withItem` を再導入した理由は commutativity と違って、`Spec` では candidate item 自身を order の比較対象に含める必要があるため
  - scan invariant の内部では `newItem.toRef` に対する `YjsLtV2'` / `YjsLeqV2'` を直接述べたい
  - そのため proof-local な active set として `old items + candidate` を持つのが自然
  - ただしこれは `SpecPortV2` の局所装置として使い、state 全体の canonical item-set 定義は引き続き `ofOldItems` に保つ
- したがって次の具体タスクは
  - `loopInvV2` が必要とする closedness / ref-membership / bounds 補題を `SpecPortV2` に集める
  - その後で old `loopInv` 補題群を 1 本ずつ `loopInvV2` に移す
- さらに `ItemSetV2.withItem` を追加したので、candidate item を old item-set に一時的に載せた reachability の表現基盤もできた
- 現時点では `withItem` の basic lookup / membership / closedness までで、wf/order invariant まではまだ載せていない
- `withItem` を本格利用する前に、より筋の良い中間案として「candidate item から current item-set を辿る reachability」を別述語に切り出した
  - `OriginReachableFromV2`
  - old `OriginReachable item x` からの forward bridge
  - `InsertInsertBridgeV2` の thin wrapper
- この形なら current state の item-set を汚さずに、commutativity の前提だけを v2 化できる
- その後 `LeanYjs/Network/Yjs/YjsNetwork.lean` の concurrent insert proof でも、この candidate-reachability wrapper を使う形へ切り替えた
  - old `h_not_reach` の手作り証明は外し、
    `toItem_*_refIn_oldItems` / `IsItemValidV2Against` / `insert_commutative_of_v2`
    を経由する構成に整理した
  - これにより network 本体は old commutativity proof の内部構造に直接依存せず、
    v2 bridge の公開 interface だけを使うようになった
- `LeanYjs/Network/Yjs/YjsNetworkBridgeV2.lean` で network valid-message 境界の thin wrapper も追加済み
  - `IsValidMessage_insert_itemSetInvariantV2`
  - `IsValidMessage_insert_itemValidV2Against`
  - `effect_list_itemSetInvariantV2`
  - `broadcastSource_valid_mono`
  - `effect_list_broadcastSource_itemSetInvariantV2`
- これで network proof は `IsValidMessage` と insert success から、直接 `newState` 側の v2 invariant を引ける
- さらに `effect_list_stateInv` を経由して、hb-consistent な operation list の評価結果から v2 invariant を直接取り出せる
- 特に causal network の broadcast source だけを仮定する標準形については、`YjsNetwork` 本体の局所 proof を再利用可能な wrapper に切り出せた
- 新しく分かった実務上のポイントは次の 2 つ
  - reverse reachability bridge は abstract `ItemSetV2` では難しいが、concrete `ItemSetV2.ofOldItems arr` では `lookup` の具体性と old unique-id から復元できる
  - したがって移行順序は「generic v2 order を先に完成」してから「concrete old-array bridge を作る」のが正しかった
  - consumer 側を直接書き換える前に `YjsArrInvariant` / `YjsStateInvariant` から v2 theorem を引く薄い wrapper 層を置くと、既存 proof の assumption shape を壊さずに差し替えを進められる
  - `InsertInsert` の `¬OriginReachable aItem bItem` については、candidate 自体を set に入れるのではなく、
    「candidate item から current item-set を辿る」専用述語 `OriginReachableFromV2` を用意するのが一番筋が良かった
  - この設計により、state の `ItemSetV2` は常に「実際に入っている item」だけを表し続けられ、
    commutativity / network の前提だけを局所的に v2 化できる

## Current State

### Recursive core representation

現状の `YjsItem` / `YjsPtr` は相互再帰になっている。

- `LeanYjs/Item.lean`

```lean
mutual
inductive YjsPtr : Type where
  | itemPtr : YjsItem -> YjsPtr
  | first : YjsPtr
  | last : YjsPtr

structure YjsItem : Type where
  origin : YjsPtr
  rightOrigin : YjsPtr
  id : YjsId
  content : A
end
```

この表現のため、pointer の `size` は item を直接辿って計算できる。
これが order 証明の再帰 measure にそのまま使われている。

### Where the current proofs depend on recursion

以下は現状の重い依存点。

- `LeanYjs/Order/ItemOrder.lean`
  - `OriginReachableStep`
  - `OriginReachable`
  - `YjsLt`
  - `YjsLeq`
  - `ConflictLt`
- `LeanYjs/Order/Totality.lean`
  - `x.size + y.size` による strong recursion
- `LeanYjs/Order/Transitivity.lean`
  - `x.size + y.size + z.size` による strong recursion
- `LeanYjs/Order/Asymmetry.lean`
  - `x.size + y.size` による decreasing argument
- `LeanYjs/Order/ItemSetInvariant.lean`
  - `not_ptr_lt_first`, `not_last_lt_ptr` が `size` に依存

### Array and algorithm side

配列・実行側は、すでに入力は id ベースの lookup を使っている。

- `LeanYjs/Algorithm/Insert/Basic.lean`
  - `IntegrateInput` は `originId` / `rightOriginId` を持つ
  - `findLeftIdx` / `findRightIdx` は id lookup

ただし、`toItem` で最終的に自己参照 item を構成し、その後の invariant / validity / commutativity proof がその具体構造を使っている。

## Target Design

## Reference type

`origin` / `rightOrigin` は、`YjsItem` 本体ではなく参照型にする。

候補は 2 つある。

### Option-based

```lean
abbrev ItemRef := Option YjsId
```

- `none` を sentinel として使う
- ただし `first` / `last` を区別できないので不適切

### Explicit ref type

推奨はこちら。

```lean
inductive ItemRef where
  | first
  | last
  | idRef : YjsId -> ItemRef
```

これにより sentinel と item-id 参照が明示的に分かれる。
現在の order 定義も sentinel を特別扱いしているので、最小の意味変更で済む。

### New item shape

```lean
structure YjsItem : Type where
  origin : ItemRef
  rightOrigin : ItemRef
  id : YjsId
  content : A
```

## ItemSet design

単なる `Set (YjsPtr A)` のまま進めるより、lookup を持つ構造体にする方がよい。
さらに、現時点の実装感では `mem` を field に持つより `lookup` を primitive にして membership を導出する方が扱いやすい。

初期案:

```lean
structure ItemSet (A : Type) where
  mem : YjsId -> Prop
  lookup : YjsId -> Option (YjsItem A)
  lookup_sound : lookup id = some item -> item.id = id
  lookup_complete : mem id -> ∃ item, lookup id = some item
  lookup_unique : lookup id = some x -> lookup id = some y -> x = y
```

現時点での推奨インターフェース:

```lean
structure ItemSet (A : Type) where
  lookup : YjsId -> Option (YjsItem A)
  lookup_sound : lookup id = some item -> item.id = id
```

この上に

```lean
IdIn id := ∃ item, lookup id = some item
ItemIn item := lookup item.id = some item
RefIn ref := ...
lookupRef ref := ...
```

を定義する。

利点:

- id uniqueness が structure の外に漏れにくい
- extensionality が `lookup` equality に還元できる
- array から作る concrete item-set と相性がよい

その上で、pointer 相当の order の引数は次のどちらかにする。

1. `ItemRef`
2. `RefOrItem` 的な和型

実用上は `ItemRef` を比較対象にし、必要に応じて item から `ItemRef.idRef item.id` を作る形でよい。

## Required structural assumptions

id 参照化すると、`closed` だけでは不十分になる。
現状はデータ構造自体が再帰的なので、ある程度「埋め込み先をそのまま辿れる」性質が自明だったが、id 参照では不正な循環が簡単に書ける。

必要な仮定は少なくとも次の 3 つ。

### 1. Closure

item が集合に属するなら、その `origin` / `rightOrigin` の参照先も同じ集合か sentinel を指す。

```lean
closed_left : item ∈ P -> ref_mem P item.origin
closed_right : item ∈ P -> ref_mem P item.rightOrigin
```

### 2. Unique ID

同じ `id` を持つ item は一意。

```lean
id_unique : x.id = y.id -> x ∈ P -> y ∈ P -> x = y
```

現時点の見立てでは、これは `ItemSet` の `lookup` を primitive にした時点で theorem として導出できる。
したがって v2 側では structural invariant の field ではなく helper theorem に落とす方がよい。

### 3. Well-founded dependency

item が参照する item を dependency edge と見た relation が `WellFounded` であること。

例えば:

```lean
def DependsOn : YjsItem A -> YjsItem A -> Prop := ...
```

に対して

```lean
wf_dependsOn : WellFounded DependsOn
```

が必要。

これがないと、

- totality
- transitivity
- asymmetry
- no-cross-origin
- reachability を使う validity

のすべてで再帰根拠が失われる。

## Core proof strategy after the refactor

## Replace structural size with rank from well-foundedness

現在の `size` は item を直接埋め込んでいるから使える。
id 参照化後は、`ItemSet` の well-foundedness から rank を作る。

イメージ:

```lean
noncomputable def refDepth (S : ItemSet A) : ItemRef -> Nat := ...
noncomputable def itemDepth (S : ItemSet A) : YjsItem A -> Nat := ...
```

欲しい性質:

- `item.origin` が item を指すなら `refDepth origin < itemDepth item`
- `item.rightOrigin` についても同様
- `YjsLt` / `YjsLeq` / `ConflictLt` の分解先で measure が確実に減る

この `depth` を使って、

- totality: `depth x + depth y`
- transitivity: `depth x + depth y + depth z`
- asymmetry: `depth x + depth y`

で strong recursion する。

## Make order explicitly depend on ItemSet

order 関係は `ItemSet` を明示引数に取る形へ変更する。

目標の形:

```lean
YjsLt (S : ItemSet A) : Nat -> ItemRef -> ItemRef -> Prop
YjsLeq (S : ItemSet A) : Nat -> ItemRef -> ItemRef -> Prop
ConflictLt (S : ItemSet A) : Nat -> YjsItem A -> YjsItem A -> Prop
OriginReachable (S : ItemSet A) : ItemRef -> ItemRef -> Prop
```

もしくは item 自身も比較対象に残したいなら、

```lean
inductive Node where
  | ref : ItemRef -> Node
  | item : YjsItem A -> Node
```

のような中間型を置く。

ただし複雑さを増やしやすいので、まずは `ItemRef` 中心で設計する方がよい。

実装の初手としては

```lean
OriginReachableStep : ItemRef -> ItemRef -> Prop
OriginReachable : ItemRef -> ItemRef -> Prop
```

を `ItemSet` 依存で定義して、item から始める場合は `item.toRef` を経由するのがよい。

## Preserve extensionality

order が `ItemSet` 依存になると、`S` と `T` が実質同じ item 集合なら order も同じ、という補題が必要になる。

必要になるもの:

- `lookup` extensionality
- `OriginReachable` extensionality
- `YjsLt` / `YjsLeq` extensionality
- `ItemSetInvariant.eq_set` の再設計版

これは現状の

- `IsClosedItemSet.eq_set`
- `ItemSetInvariant.eq_set`

の後継になる。

## Work Breakdown

## Phase 0: Create a parallel v2 foundation

まず既存実装を直接壊さず、新しい基盤を別名で追加する。

候補ファイル:

- `LeanYjs/ItemRef.lean`
- `LeanYjs/Order/ItemOrderV2.lean`
- `LeanYjs/Order/ItemSetInvariantV2.lean`
- `LeanYjs/Algorithm/Invariant/BasicV2.lean`

ここでは既存 theorem はまだ書き換えない。

目的:

- 新データモデルを固定する
- 必要な補題の集合を見積もる
- order の最小コアが本当に回るかを確認する

## Phase 1: Data model split

`YjsItem` の新定義と `ItemRef` を導入する。

この段階で作るもの:

- `ItemRef`
- `ItemRef.toOptionId?` などの補助関数
- sentinel 判定
- `lookupRef : ItemSet A -> ItemRef -> Option (YjsItem A)` または同等物

注意点:

- ここで既存 `YjsPtr` を即削除しない
- bridge 関数を用意して、旧 API と新 API を並行利用できる状態にする

## Phase 2: Rebuild order core

最重要フェーズ。

対象:

- `OriginReachable`
- `YjsLt`
- `YjsLeq`
- `ConflictLt`

やること:

- 現行 constructor を id-ref 版に翻訳する
- `lookup` を介して参照先を辿る
- decreasing proof を `size` ではなく `depth` / `rank` で立て直す

この段階で欲しい主要補題:

- `refDepth_origin_lt_itemDepth`
- `refDepth_rightOrigin_lt_itemDepth`
- `reachable_decreases`
- `lookup_id_unique`
- `lookup_closed_origin`
- `lookup_closed_rightOrigin`

## Phase 3: Reprove order meta-theorems

対象:

- `LeanYjs/Order/Totality.lean`
- `LeanYjs/Order/Transitivity.lean`
- `LeanYjs/Order/Asymmetry.lean`
- `LeanYjs/Order/NoCrossOrigin.lean`

やること:

- `size` ベース再帰を `depth` ベース再帰へ移行
- `P x` の代わりに「`x` が `S` で well-formed」に近い仮定へ整理
- `eq_set` 系補題を `lookup` extensionality ベースで再構築

工数メモ:

- このフェーズが全体で最も重い
- totality と transitivity が hardest part
- asymmetry は totality / transitivity の新補題が揃えば追従しやすい

## Phase 4: Rebuild array-level invariants

対象:

- `LeanYjs/Algorithm/Invariant/Basic.lean`
- `LeanYjs/Algorithm/Invariant/YjsArray.lean`

やること:

- `ArrSet` を item membership + id lookup ベースに再定義
- `ArrSetClosed` を参照解決版に差し替える
- `YjsArrInvariant` の `closed` / `item_set_inv` / `sorted` の意味を調整

重要ポイント:

- array は順序付き concrete container
- `ItemSet` は order / reachability が依存する abstract view

この 2 つを分離しておくと proof が整理しやすい。

## Phase 5: Update executable insert layer

対象:

- `LeanYjs/Algorithm/Insert/Basic.lean`

この層は比較的軽い。

やること:

- `IntegrateInput.toItem` を非再帰 item を返すよう変更
- `findPtrIdx` 相当は不要または大幅簡略化
- `mkItemByIndex` / `getPtrExcept` は `ItemRef` を返すよう変更

見込み:

- 実装量は小さい
- 既存の id lookup 実装をかなり流用できる

## Phase 6: Update insert validity and preservation proofs

対象:

- `LeanYjs/Algorithm/Insert/Spec.lean`

やること:

- `IsItemValid` を新しい `OriginReachable` / `YjsLt` ベースに変更
- `YjsArrInvariant_integrate`
- `YjsArrInvariant_integrateSafe`
- `YjsStateInvariant_insert`

注意点:

- このファイルは `origin/rightOrigin` の field を非常に多く使っている
- order 側の補題不足がここで一気に露出する

工数は大きい。
order 層に次ぐ難所。

## Phase 7: Update commutativity

対象:

- `LeanYjs/Algorithm/Commutativity/InsertInsert.lean`

やること:

- concurrent insert の reachability 仮定を新定義に合わせる
- ただしこれは `ofOldItems arr` への単純置換ではなく、candidate item を含む拡張 set の設計が先に必要
- `integrate_ok_commutative`
- `integrate_commutative`
- `insert_commutative`

特に重い理由:

- `OriginReachable`
- `item.isValid`
- `YjsArrInvariant`

の 3 つに同時依存しているため。

`InsertDelete` と `DeleteDelete` は比較的軽い。

## Phase 8: Update network glue

対象:

- `LeanYjs/Network/Yjs/YjsNetwork.lean`

やること:

- `IsValidMessage`
- `stateInv_effect`
- prefix split / toItem bridge 補題
- convergence proof が必要とする validity bridge

見込み:

- theorem 数は多いが、主に前段の追従
- 根本的な新規アイデアより、補題の差し替えが中心

## File-by-file impact

### Very high impact

- `LeanYjs/Item.lean`
- `LeanYjs/ItemSet.lean`
- `LeanYjs/Order/ItemOrder.lean`
- `LeanYjs/Order/ItemSetInvariant.lean`
- `LeanYjs/Order/Totality.lean`
- `LeanYjs/Order/Transitivity.lean`
- `LeanYjs/Order/Asymmetry.lean`
- `LeanYjs/Order/NoCrossOrigin.lean`
- `LeanYjs/Algorithm/Insert/Spec.lean`
- `LeanYjs/Algorithm/Commutativity/InsertInsert.lean`

### Medium impact

- `LeanYjs/Algorithm/Invariant/Basic.lean`
- `LeanYjs/Algorithm/Invariant/YjsArray.lean`
- `LeanYjs/Algorithm/Insert/Basic.lean`
- `LeanYjs/Algorithm/YString.lean`
- `DiffTestRunner.lean`

### Lower impact

- `LeanYjs/Algorithm/Delete/*`
- `LeanYjs/Algorithm/Commutativity/InsertDelete.lean`
- `LeanYjs/Algorithm/Commutativity/DeleteDelete.lean`
- `LeanYjs/Network/Yjs/YjsNetwork.lean`

lower impact といっても証明修正量がゼロという意味ではない。
新 API に追従するための書き換えは必要。

## Proposed minimal interfaces

実装着手前に先に固定したい最小 interface を書いておく。

## `ItemRef`

```lean
inductive ItemRef where
  | first
  | last
  | idRef : YjsId -> ItemRef
deriving Repr, DecidableEq
```

## `lookupRef`

```lean
def lookupRef (S : ItemSet A) : ItemRef -> Option (YjsItem A)
```

性質:

- `lookupRef first = none`
- `lookupRef last = none`
- `lookupRef (idRef id) = S.lookup id`

## membership

```lean
def RefIn (S : ItemSet A) : ItemRef -> Prop
```

意味:

- sentinel は常に in
- `idRef id` は `S.mem id`

## dependency

```lean
def DependsOn (S : ItemSet A) (x y : YjsItem A) : Prop :=
  x.origin = .idRef y.id \/ x.rightOrigin = .idRef y.id
```

もしくは参照解決ベースで

```lean
def DependsOn (S : ItemSet A) (x y : YjsItem A) : Prop :=
  lookupRef S x.origin = some y \/ lookupRef S x.rightOrigin = some y
```

後者の方が theorem では扱いやすい可能性が高い。

## invariant

```lean
structure ItemSetInvariant (S : ItemSet A) where
  closed_left : ...
  closed_right : ...
  id_unique : ...
  wf_dependsOn : WellFounded (DependsOn S)
  origin_lt_rightOrigin : ...
  origin_nearest_reachable : ...
```

現行の `origin_not_leq` は名前を変えた方がよい。
意味としては「well-formed item は left origin < right origin」であり、`origin_lt_rightOrigin` の方が直感的。

## Risks

## Risk 1: `Set`-only `ItemSet` is too weak

単なる `Set (YjsItem A)` または `Set YjsId` だと、

- 参照解決
- extensionality
- uniqueness
- closure の transport

が毎回 theorem の前提に漏れ出しやすい。

対策:

- 最初から `lookup` を持つ structure にする

## Risk 2: Well-foundedness is underspecified

「下に closed」だけでは循環を除けない。

対策:

- `wf_dependsOn` を invariant に含める
- 可能なら `Acc` を返す補題を早めに整備する

## Risk 3: order extensionality becomes noisy

`S` 引数を増やすと、既存の証明で set equality / lookup equality を何度も通す必要が出る。

対策:

- `lookupExt`
- `RefIn_ext`
- `OriginReachable_ext`
- `YjsLt_ext`

を早い段階でまとめて作る

## Risk 4: `Insert/Spec` で proof search が崩れる

現状は具体的な `item.origin` / `item.rightOrigin` を直接展開できる場面が多い。
id-ref 化すると、lookup を一段挟むため簡単な `simp` では落ちなくなる。

対策:

- `simp` lemma の設計を早めに行う
- `lookupRef` と `RefIn` に関する `[simp]` 補題を揃える

## Validation plan

実作業の検証順は AGENTS に合わせて次で回す。

1. 対象ファイルの LSP diagnostics
2. `lake env lean <file>`
3. 必要になったら `lake build`

フェーズごとの完了条件:

### Order core

- `ItemOrderV2.lean` が通る
- totality / transitivity / asymmetry の statement が閉じる

### Array invariant

- `YjsArrInvariant` の新定義で基礎補題が通る
- `same_yjs_set_unique` 相当が復元できる

### Insert

- `YjsStateInvariant_insert` が復元できる

### Commutativity

- `insert_commutative` が復元できる

### Network

- `YjsOperationNetwork_converge'` が再び通る

## Recommended implementation order

最も安全な順番を固定しておく。

1. `ItemRef` と `ItemSet` v2 を追加
2. `DependsOn` / `wf` / `depth` を追加
3. `OriginReachable` / `YjsLt` / `YjsLeq` / `ConflictLt` を v2 で再実装
4. totality / transitivity / asymmetry / no-cross-origin を v2 で再証明
5. `ArrSet` / `YjsArrInvariant` を v2 化
6. `IntegrateInput.toItem` と insert 実装を追従
7. `Insert/Spec` を移植
8. `InsertInsert` を移植
9. network glue を追従
10. 旧定義を削除

## What not to do

以下は避ける。

- 既存 `YjsItem` を即座に置き換えて全ファイルを一気に直す
- `ItemSet := Set ...` のまま proof obligations を theorem ごとに増やす
- `wf` なしで closure だけで押し切ろうとする
- order と array invariant を同時に全面書き換えする

big-bang 方式だと、どこで必要補題が不足しているのか見えにくくなる。

## Concrete first milestone

最初のマイルストーンは小さく切る。

### Milestone 1

新しい基盤ファイルを追加して、次だけを通す。

- `ItemRef`
- `ItemSet` v2
- `lookupRef`
- `RefIn`
- `DependsOnId`
- `WellFoundedItemSetV2.induction`

まだ algorithm には触らない。

### Milestone 2

`ItemOrderV2.lean` で次だけ通す。

- `OriginReachable`
- `YjsLt`
- `YjsLeq`
- 基本 constructor helper

### Milestone 3

`TotalityV2`, `TransitivityV2`, `AsymmetryV2` を通す。

この 3 つが通った時点で、設計が成立するかどうかはほぼ判定できる。

## Final assessment

この refactor は妥当で、長期的には設計をかなり健全にする。
ただし工数は order の証明基盤に集中する。

見積もりとしては:

- 実装コードの差し替えは小から中
- order 証明の再建は大
- insert spec / insert-insert commutativity の追従も大

したがって、最初にやるべきことは field 変更ではなく、`ItemSet` 引数つき order を支える最小基盤の固定である。

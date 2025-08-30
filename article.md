# Yjsのコアアルゴリズムの正しさをLean4で証明する

## 1. はじめに

Yjs [^1] はJavaScriptによるCRDTの実装で、私の知る限り世界で最も使われているCRDTライブラリです。
YjsのアルゴリズムはYATA論文 [^1] によって提案され、同論文にて正しさが証明されたとされています。
ここでいう正しさとは収束性、つまり因果関係に逆らわないようなどんな順番で操作が行われても結果の状態が一意に定まることです。
YATA論文では特に要素の挿入を行うアルゴリズムである `integrate` について収束性の証明が与えられています。
その証明は、

1. YATAの挿入要素間の間である全順序が定義されることと、
2. YATAアルゴリズムがその全順序に従って要素を挿入すること

の2つの定理からYATAが収束することを証明していますが、1は正しさを確信するのは難しい式変形によってその証明が行われ、
2については証明は与えられていません。

さらに、厳密に言うとYjsアルゴリズムとYATAは厳密には違います。
後に示すように、YATA論文に載っているintegrateアルゴリズムは収束しません。

そのような問題から私はYjsアルゴリズムintegrateアルゴリズムのコア部分をLean4で形式化・証明しようと試みてきました。
Lean4を使ったのは `integrate` のような十数行程度のアルゴリズムでも、紙とペンでは証明に誤りがないことを保証するのが難しいからです。

私は `integrate` アルゴリズムがある条件下で可換であること [^1] を証明しました。
可換性はCRDT (特にop-based CRDT) の収束性の十分条件の1つです。
この記事ではLean4による形式化と証明について紹介したいと思います。

[^1] op-based CRDTではある種の可換性から収束性が導かれることが証明されていますが、私の示した可換性がその可換性と一致するかはまだ分かっていません。
私の示した可換性は `InsertOk a list` という条件を要求していて、これはおそらく挿入される要素を作る操作とop-based CRDTが仮定するcausal deliveryから成立する条件なので問題ないと思うのですがそれを確かめるのは今後の課題です。

## 2. Yjs の基本概念

Yjsは文字列、リスト、辞書等のデータ型とそれらに対する操作をサポートしたCRDTライブラリです。
CRDTは簡単に言えば異なる場所で同期せずに変更を行っても適切に変更データを同期することで一意に収束することが保証されたデータ構造です。

```
ここにYjsのナイスな実行例が入る。
```

YjsはItemというオブジェクトの双方向連結リストにより状態を管理します。
(リスト以外のデータ構造もこの双方向連結リストとして表現されます。)
Itemは大雑把に言うと

- 挿入時に直前にいた要素 (origin)
- 挿入時に直後にいた要素 (rightOrigin)
- 一意な操作のId (clientIdとカウンタ値の組)
- 中身

の組であり、Yjsではorigin/rightOrigin/clientIdを用いて適切な順序でItemを並び替えることで収束性を保証しています。
削除は削除フィールドを有効にするだけのいわゆる論理削除によって実現されていて、これは収束性の議論にはほとんど関わらないため、今回は挿入のみを扱います。

挿入は挿入したい位置の両隣からItemを生成し、そのItemを以下のintegrateアルゴリズムに渡すことで行われます。
ほかのクライアントと同期する際には、生成したItemのみを渡して同じようにintegrateで挿入した要素を取り込みます。

### integrateアルゴリズム

integrateの入力は挿入したいItem `newItem` と現在のリスト `items` です。`integrate` はoriginからrightOriginまでの要素`item`のうち、`neweItem < item` を満たす最小の`item`を探し、`item`の左に`newItem` を挿入します。
ここで、Item間の順序関係 `<` は挿入位置を決めるための順序関係であり、入力のリスト `items` は `<`によってソート済みであると仮定します。

すると、もし

- `<`が全順序で、
- `integrate`が正しい位置に`newItem`を挿入するなら、

integrateは可換性を満たす、つまりどんな順序でItemを挿入しても同じ状態に収束することがなんとなくイメージできると思います。

### YATAの正当性証明

YATA論文での順序関係の定義は以下のようになります。

$$
YATA論文の引用
$$

`integrate`はYATAでは以下のようなアルゴリズムです。

```
integrateアルゴリズムの引用
```

しかしこのアルゴリズムの正しさをすぐに確信することは難しいと思います。このアルゴリズムが単純に各要素と新規の要素を比較しているだけでは無いことは見てわかると思います。
これはYjsが定義する比較はorigin/rightOriginを遡る必要があり、高速に評価することが難しいためです。
また、dest/scanningという変数も鬼門です。iでbreakしたときの挿入位置が別の変数destで与えられるというのはソート済み配列への挿入というアルゴリズムとしては特殊な形をしていると思います。

Lean4の形式化ではこの規則は用いず、新しく順序関係を再定義しました。当然従うべき規則のみを用いていて、その規則が推移律と反対称律を満たすことを証明しました。
integrateの検証ではループ不変量を設計し、なぜdestまで戻ることになるのかということにも自分なりに直感的な形で形式的な証明を与えました。

## 3. 形式検証のアプローチと証明戦略

### 3.1 形式検証の基本方針

(TODO: LLM)
- なぜ Lean4 を選択したか -> 10年前学生時代にCoqのみを使っていたが、別の定理証明支援系を使いたくなった、LLMの恩恵が受けられるかも？（結果としてCopilotの補完以外使うことはほとんど無かった）
- アルゴリズム -> https://github.com/josephg/reference-crdts
  - 双方向連結リスト形式のアルゴリズムは定理証明支援系での形式化は本質的でない難しさを生む
  - 今回は配列ベースのjosephgによる実装を対象とした
- 証明すべき性質の特定 -> integrateが可換であること。
  - 可換性から収束性が導かれるのはop-based CRDTの性質から成り立つ。
  - 実際に、私が証明した性質が収束性につながるか確認するのは今後やっていきたい
    - 例えばMartin KleppmennたちのチームのIsabelleによるCRDTの形式化につなげるとか、Iris分離論理によるop-based CRDTの実装につなげるとか考えられる。
- 段階的な証明戦略の設計
  - YATA論文にならって
    1. YATA順序の全順序性の証明
    2. integrateアルゴリズムの正当性
    の順番で示した。
- チャレンジ
  - YATA論文の定義はwell formedな再帰的定義になっていない
    - productivityに反するのでLean4で定義できない
    - YATAは踏襲せずにもっと直感的な定義を目指す
  - アルゴリズムのループ不変量の設計
    - なぜ決着がついたときにdestまで戻していいのか？という疑問に答える必要がある
      - TODO: アイデアの概略

## 4. Lean による形式モデル化

### 4.1 データ構造の定義

- `YjsItem`と`YjsPtr`の相互再帰定義
- `ActorId`の型定義

### 4.2 順序関係の形式化

#### ItemSet

- YATAは任意の (conflictingな) 要素についての全順序性を仮定したが、すぐにわかるようにそんなことはない。origin=last, rightOrigin=firstとすればあきらかにこれは循環する。
- これと似ているが、任意の2要素a, bについて、その間に要素を挿入すれば a < bとできる。
  - この問題をYATA論文には言及がない
- このような状況を防ぐには、順序を定義する要素には制限が必要。
- 今回は全順序はあるYjsPtrの部分集合に対して定義されるものとし、その部分集合に制限をつけることで定義した。
  - ItemSet.lean/ItemSetInvariant.lean
  - origin/rightOriginについて閉じていることと、上のような状況を排除するための不変条件

#### 順序関係の定義

### 4.3 配列の不変条件

- `YjsArrInvariant`の定義
- ソート済み配列の性質
- 閉じた集合（`IsClosedItemSet`）の概念

## 5. 主要な定理と証明戦略

### 5.1 順序関係の基本性質

- 全順序性の証明（`yjs_lt_total`）
- 推移性の証明 (`yjs_lt_trans`) / 反対称性の証明（`yjs_lt_anti_symm`）

これらはitemのサイズに対する数学的帰納法を用いることで証明できます。
反対称律 (\forall a b, a < b -> b < a -> False) の方はa, bのサイズの和に対する帰納法、
推移律 (\forall a b c, a < b -> b < c -> a < c) の方はa, b, cのサイズの和に対する帰納法を用います。

これら2つの性質は一方の順序関係の定義によって一方の性質が楽になるがもう一方の性質の証明が難しくなります。
規則の推移閉包をとることで推移律の証明は容易になるのですが、反対称律をサイズに対する数学的帰納法で示すことは難しくなります。なぜなら、前提のうちの1つ、例えばa < bが推移律で導かれるケースではa < c, c < aという形の前提が出てきてしまい、項のサイズが小さくならないためです。
一方で推移閉包をとらずに規則を小さく保つことで反対称律は証明しやすくなりますが、今度は推移律を自力で証明する必要があります。
結果としては後者のやり方でうまくいきましたが、しばらく前者のやり方にこだわっていたためなかなか証明が進まず苦労しました。
(プログラミング言語の形式かなんかでは推移閉包をとって定義とするのは自然なやり方なので、それにこだわってしまったという背景があります。)

### 5.2 integrate アルゴリズムの健全性

```
theorem integrate_commutative (a b : YjsItem A) (arr1 arr2 arr3 arr2' arr3' : Array (YjsItem A)) :
  YjsArrInvariant arr1.toList
  -> a.id ≠ b.id
  -> InsertOk arr1 a
  -> InsertOk arr1 b
  -> integrate a arr1 = Except.ok arr2
  -> integrate b arr2 = Except.ok arr3
  -> integrate b arr1 = Except.ok arr2'
  -> integrate a arr2' = Except.ok arr3'
  -> arr3 = arr3' := by
```

主定理は、挿入が順序によらないこと (可換であること) を証明しました。
```lean
  -> integrate a arr1 = Except.ok arr2
  -> integrate b arr2 = Except.ok arr3
  -> integrate b arr1 = Except.ok arr2'
  -> integrate a arr2' = Except.ok arr3'
  -> arr3 = arr3' := by
```
の部分だけ見れば、`arr1`というリストに`a`→`b`という順番で挿入したときと`b`→`a`という順番で挿入したときで結果が一致するということを意味しています。

`InsertOk arr1 a`と言う性質は、arr1に対してaが挿入可能な要素であるという仮定です。具体的な定義は下のようになっています。

```
structure InsertOk (arr : Array (YjsItem A)) (newItem : YjsItem A) where
  not_mem : (∀ x ∈ arr, x ≠ newItem)
  origin_in : ArrSet arr.toList newItem.origin
  rightOrigin_in : ArrSet arr.toList newItem.rightOrigin
  origin_lt_rightOrigin : YjsLt' (ArrSet arr.toList) newItem.origin newItem.rightOrigin
  reachable_YjsLeq' : (∀ (x : YjsPtr A),
      OriginReachable (YjsPtr.itemPtr newItem) x →
      YjsLeq' (ArrSet arr.toList) x newItem.origin ∨ YjsLeq' (ArrSet arr.toList) newItem.rightOrigin x)
  id_eq_YjsLeq' : (∀ (x : YjsItem A),
      ArrSet arr.toList (YjsPtr.itemPtr x) →
      x.id = newItem.id →
      YjsLeq' (ArrSet arr.toList) (YjsPtr.itemPtr x) newItem.origin ∨
        YjsLeq' (ArrSet arr.toList) newItem.rightOrigin (YjsPtr.itemPtr x))

```
1. not_mem -> aが未挿入であること
2. origin_in/rightOrigin_in -> aのorigin/rightOriginがすでにリストに存在すること
3. origin_lt_rightOrigin -> aのorigin < bのoriginであること
4. reachable_YjsLeq -> xからorigin/rightOriginを通じて到達可能である要素は、aとconflictしないこと
5. id_eq_YjsLeq' -> xと同じclientIDを持つ要素は、aとconflictしないこと

1~3は分かりやすいと思います。1は (TODO: LLM), 2は挿入時に隣り合っていた要素はintegrate時にも隣り合うこと、つまり因果性の仮定です。3は前述した循環を許さないためです。
4, 5はわかりづらいのですが、これは到達可能な要素や同じClientIdを持つ要素は挿入時に配列に存在しているはずなので、これらとconflictすることはないという仮定になります。
これも因果性の仮定 (localに依存していた要素はremoteでも印が順序を保つ) になります。

これらの仮定を満たさないItemがintegrateの入力となってしまうと、全順序型も保てずに収束しなくなります。
当然insert等のYjsのAPIから生成されたItemはこれらの仮定を満たすべきですが[^1]、悪意のあるクライアントからこれらのパケットが送られてくる可能性があります。
これはすなわちYjsがビザンチン耐性が無いこと (悪意のあるピアや故障したピアから送られてくるパケットに対する耐性が無い) を示しています。

[^1]:  証明は今後の課題です。

さてこの定理の証明ですが、以下のような流れで行いました。

1. integrateアルゴリズムはソート済み配列を保存する (入力がソート済みなら出力もソート済み)
2. 集合として要素が等しい配列をソートする方法は1つだけ
3. 1, 2よりarrがソート済みならarrにa, bをintegrateした結果は`arr ∪ a ∪ b`のソート済み配列なので、integrateは可換

2, 3はそれほど難しくないので1について証明を概説します。

`integrate`はループで定義されているため、ループ不変量を用いて証明しました。
integrateアルゴリズムのループ不変量は以下の図によって表されます。

1. i < destとなるiについて、arr[i] < newItem
2. dest \leq i < currentとなるiについて、
  arr[i].origin = newItem.originかつnewItem.id < arr[i].id または、
  arr[dest] < arr[i].origin

2番目の条件はdestからcurrentの間にある要素についてはまだnewItemとの順序が未確定であることを意味しています。
これが確定するのはいつかというと、`newItem < arr[i]`となる`i`をみつけたときです。
このとき実は`dest \leq i < current`のすべてのiについて、`newItem < arr[i]`であることがわかります。
(loopInv_YjsLt')
これらを組み合わせると、ループを抜けたときnewItemを挿入するべき位置、つまり`newItem`より大きい最小の要素は`arr[dest]`であることがわかります。
よって、integrateは正しい位置に挿入していることがわかります。

これはざっくりとした証明の方針であり、実際の証明は様々なコーナーケースをカバーする必要があり大分長いのですが、もしよければ読んでみてください。

## 現在の課題と今後の展望

- 証明した可換性が収束を導くことの証明
- insert等の基本操作によって生成されるItemがinsertOkを満たすこと

## 10. まとめ

今回はYjsのintegrateアルゴリズムの形式証明を行いました。
YATA論文を最初に知ってから数年がたつのですが、証明を読んで納得できなかったのがついに証明を作れた (しかもLean4で!) というのはかなりよかったと思います。
CRDTの収束性のような分散環境でのアルゴリズムの証明を正しく行うのは難しく、その点でLeanのような定理証明支援系は今後も使われていくのでは無いかと思います。

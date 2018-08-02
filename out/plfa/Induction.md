---
title     : "Induction: Proof by Induction"
layout    : page
permalink : /Induction/
---

<pre class="Agda">{% raw %}<a id="108" class="Keyword">module</a> <a id="115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}" class="Module">plfa.Induction</a> <a id="130" class="Keyword">where</a>{% endraw %}</pre>

> Induction makes you feel guilty for getting something out of nothing
> ... but it is one of the greatest ideas of civilization.
> -- Herbert Wilf

Now that we've defined the naturals and operations upon them, our next
step is to learn how to prove properties that they satisfy.  As hinted
by their name, properties of *inductive datatypes* are proved by
*induction*.


## Imports

We require equivality as in the previous chapter, plus the naturals
and some operations upon them.  We also import a couple of new operations,
`cong`, `sym`, and `_≡⟨_⟩_`, which are explained below.
<pre class="Agda">{% raw %}<a id="743" class="Keyword">import</a> <a id="750" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="788" class="Symbol">as</a> <a id="791" class="Module">Eq</a>
<a id="794" class="Keyword">open</a> <a id="799" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="802" class="Keyword">using</a> <a id="808" class="Symbol">(</a><a id="809" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="812" class="Symbol">;</a> <a id="814" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="818" class="Symbol">;</a> <a id="820" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a><a id="824" class="Symbol">;</a> <a id="826" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#560" class="Function">sym</a><a id="829" class="Symbol">)</a>
<a id="831" class="Keyword">open</a> <a id="836" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3861" class="Module">Eq.≡-Reasoning</a> <a id="851" class="Keyword">using</a> <a id="857" class="Symbol">(</a><a id="858" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin_</a><a id="864" class="Symbol">;</a> <a id="866" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">_≡⟨⟩_</a><a id="871" class="Symbol">;</a> <a id="873" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">_≡⟨_⟩_</a><a id="879" class="Symbol">;</a> <a id="881" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">_∎</a><a id="883" class="Symbol">)</a>
<a id="885" class="Keyword">open</a> <a id="890" class="Keyword">import</a> <a id="897" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="906" class="Keyword">using</a> <a id="912" class="Symbol">(</a><a id="913" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="914" class="Symbol">;</a> <a id="916" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="920" class="Symbol">;</a> <a id="922" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="925" class="Symbol">;</a> <a id="927" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="930" class="Symbol">;</a> <a id="932" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="935" class="Symbol">;</a> <a id="937" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="940" class="Symbol">)</a>{% endraw %}</pre>


## Associativity

One property of addition is that it is *associative*, that is, that the
location of the parentheses does not matter:

    (m + n) + p ≡ m + (n + p)

Here `m`, `n`, and `p` are variables that range over all natural numbers.

We can test the proposition by choosing specific numbers for the three
variables.
<pre class="Agda">{% raw %}<a id="1292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#1292" class="Function">_</a> <a id="1294" class="Symbol">:</a> <a id="1296" class="Symbol">(</a><a id="1297" class="Number">3</a> <a id="1299" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1301" class="Number">4</a><a id="1302" class="Symbol">)</a> <a id="1304" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1306" class="Number">5</a> <a id="1308" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="1310" class="Number">3</a> <a id="1312" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1314" class="Symbol">(</a><a id="1315" class="Number">4</a> <a id="1317" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1319" class="Number">5</a><a id="1320" class="Symbol">)</a>
<a id="1322" class="Symbol">_</a> <a id="1324" class="Symbol">=</a>
  <a id="1328" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="1338" class="Symbol">(</a><a id="1339" class="Number">3</a> <a id="1341" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1343" class="Number">4</a><a id="1344" class="Symbol">)</a> <a id="1346" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1348" class="Number">5</a>
  <a id="1352" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="1360" class="Number">7</a> <a id="1362" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1364" class="Number">5</a>
  <a id="1368" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="1376" class="Number">12</a>
  <a id="1381" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="1389" class="Number">3</a> <a id="1391" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1393" class="Number">9</a>
  <a id="1397" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="1405" class="Number">3</a> <a id="1407" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1409" class="Symbol">(</a><a id="1410" class="Number">4</a> <a id="1412" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1414" class="Number">5</a><a id="1415" class="Symbol">)</a>
  <a id="1419" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>{% endraw %}</pre>
Here we have displayed the computation as a chain of equations,
one term to a line.  It is often easiest to read such chains from the top down
until one reaches the simplest term (in this case, `12`), and
then from the bottom up until one reaches the same term.

The test reveals that associativity is perhaps not as obvious as first
it appears.  Why should `7 + 5` be the same as `3 + 9`?  We might want
to gather more evidence, testing the proposition by choosing other
numbers.  But---since there are an infinite number of
naturals---testing can never be complete.  Is there any way we can be
sure that associativity holds for *all* the natural numbers?

The answer is yes! We can prove a property holds for all naturals using
*proof by induction*.


## Proof by induction

Recall the definition of natural numbers consists of a *base case*
which tells us that `zero` is a natural, and an *inductive case*
which tells us that if `m` is a natural then `suc m` is also a natural.

Proof by induction follows the structure of this definition.  To prove
a property of natural numbers by induction, we need prove two cases.
First is the *base case*, where we show the property holds for `zero`.
Second is the *inductive case*, where we assume the the property holds for
an arbitrary natural `m` (we call this the *inductive hypothesis*), and
then show that the property must also hold for `suc m`.

If we write `P m` for a property of `m`, then what we need to
demonstrate are the following two inference rules:

    ------
    P zero

    P m
    ---------
    P (suc m)

Let's unpack these rules.  The first rule is the base case, and
requires we show that property `P` holds for `zero`.  The second rule
is the inductive case, and requires we show that if we assume the
inductive hypothesis, namely that `P` holds for `m`, then it follows that
`P` also holds for `suc m`.

Why does this work?  Again, it can be explained by a creation story.
To start with, we know no properties.

    -- in the beginning, no properties are known

Now, we apply the two rules to all the properties we know about.  The
base case tells us that `P zero` holds, so we add it to the set of
known properties.  The inductive case tells us that if `P m` holds (on
the day before today) then `P (suc m)` also holds (today).  We didn't
know about any properties before today, so the inductive case doesn't
apply.

    -- on the first day, one property is known
    P zero

Then we repeat the process, so on the next day we know about all the
properties from the day before, plus any properties added by the rules.
The base case tells us that `P zero` holds, but we already
knew that. But now the inductive case tells us that since `P zero`
held yesterday, then `P (suc zero)` holds today.

    -- on the second day, two properties are known
    P zero
    P (suc zero)

And we repeat the process again. Now the inductive case
tells us that since `P zero` and `P (suc zero)` both hold, then
`P (suc zero)` and `P (suc (suc zero))` also hold. We already knew about
the first of these, but the second is new.

    -- on the third day, three properties are known
    P zero
    P (suc zero)
    P (suc (suc zero))

You've got the hang of it by now.

    -- on the fourth day, four properties are known
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))

The process continues.  On the *n*th day there will be *n* distinct
properties that hold.  The property of every natural number will appear
on some given day.  In particular, the property `P n` first appears on
day *n+1*.


## Our first proof: associativity

To prove associativity, we take `P m` to be the property

    (m + n) + p ≡ m + (n + p)

Here `n` and `p` are arbitrary natural numbers, so if we can show the
equation holds for all `m` it will also hold for all `n` and `p`.
The appropriate instances of the inference rules are:

    -------------------------------
    (zero + n) + p ≡ zero + (n + p)

    (m + n) + p ≡ m + (n + p)
    ---------------------------------
    (suc m + n) + p ≡ suc m + (n + p)

If we can demonstrate both of these, then associativity of addition
follows by induction.

Here is the proposition's statement and proof.
<pre class="Agda">{% raw %}<a id="+-assoc"></a><a id="5655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5655" class="Function">+-assoc</a> <a id="5663" class="Symbol">:</a> <a id="5665" class="Symbol">∀</a> <a id="5667" class="Symbol">(</a><a id="5668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5668" class="Bound">m</a> <a id="5670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5670" class="Bound">n</a> <a id="5672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5672" class="Bound">p</a> <a id="5674" class="Symbol">:</a> <a id="5676" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="5677" class="Symbol">)</a> <a id="5679" class="Symbol">→</a> <a id="5681" class="Symbol">(</a><a id="5682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5668" class="Bound">m</a> <a id="5684" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5670" class="Bound">n</a><a id="5687" class="Symbol">)</a> <a id="5689" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5691" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5672" class="Bound">p</a> <a id="5693" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="5695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5668" class="Bound">m</a> <a id="5697" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5699" class="Symbol">(</a><a id="5700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5670" class="Bound">n</a> <a id="5702" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5672" class="Bound">p</a><a id="5705" class="Symbol">)</a>
<a id="5707" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5655" class="Function">+-assoc</a> <a id="5715" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="5720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5720" class="Bound">n</a> <a id="5722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5722" class="Bound">p</a> <a id="5724" class="Symbol">=</a>
  <a id="5728" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="5738" class="Symbol">(</a><a id="5739" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="5744" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5746" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5720" class="Bound">n</a><a id="5747" class="Symbol">)</a> <a id="5749" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5722" class="Bound">p</a>
  <a id="5755" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="5763" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5720" class="Bound">n</a> <a id="5765" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5722" class="Bound">p</a>
  <a id="5771" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
   <a id="5778" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="5783" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5785" class="Symbol">(</a><a id="5786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5720" class="Bound">n</a> <a id="5788" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5722" class="Bound">p</a><a id="5791" class="Symbol">)</a>
  <a id="5795" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>
<a id="5797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5655" class="Function">+-assoc</a> <a id="5805" class="Symbol">(</a><a id="5806" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5810" class="Bound">m</a><a id="5811" class="Symbol">)</a> <a id="5813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5813" class="Bound">n</a> <a id="5815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5815" class="Bound">p</a> <a id="5817" class="Symbol">=</a>
  <a id="5821" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="5831" class="Symbol">(</a><a id="5832" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5810" class="Bound">m</a> <a id="5838" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5840" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5813" class="Bound">n</a><a id="5841" class="Symbol">)</a> <a id="5843" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5845" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5815" class="Bound">p</a>
  <a id="5849" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="5857" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5861" class="Symbol">(</a><a id="5862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5810" class="Bound">m</a> <a id="5864" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5866" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5813" class="Bound">n</a><a id="5867" class="Symbol">)</a> <a id="5869" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5871" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5815" class="Bound">p</a>
  <a id="5875" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="5883" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5887" class="Symbol">((</a><a id="5889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5810" class="Bound">m</a> <a id="5891" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5813" class="Bound">n</a><a id="5894" class="Symbol">)</a> <a id="5896" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5898" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5815" class="Bound">p</a><a id="5899" class="Symbol">)</a>
  <a id="5903" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="5906" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a> <a id="5911" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5915" class="Symbol">(</a><a id="5916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5655" class="Function">+-assoc</a> <a id="5924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5810" class="Bound">m</a> <a id="5926" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5813" class="Bound">n</a> <a id="5928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5815" class="Bound">p</a><a id="5929" class="Symbol">)</a> <a id="5931" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="5937" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5941" class="Symbol">(</a><a id="5942" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5810" class="Bound">m</a> <a id="5944" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5946" class="Symbol">(</a><a id="5947" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5813" class="Bound">n</a> <a id="5949" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5815" class="Bound">p</a><a id="5952" class="Symbol">))</a>
  <a id="5957" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="5965" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5810" class="Bound">m</a> <a id="5971" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5973" class="Symbol">(</a><a id="5974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5813" class="Bound">n</a> <a id="5976" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#5815" class="Bound">p</a><a id="5979" class="Symbol">)</a>
  <a id="5983" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>{% endraw %}</pre>
We have named the proof `+-assoc`.  In Agda, identifiers can consist of
any sequence of characters not including spaces or the characters `@.(){};_`.

Let's unpack this code.  The signature states that we are
defining the identifier `+-assoc` which provide evidence for the
proposition:

    ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

The upside down A is pronounced "for all", and the proposition
asserts that for all natural numbers `m`, `n`, and `p` that
the equation `(m + n) + p ≡ m + (n + p)` holds.  Evidence for the proposition
is a function that accepts three natural numbers, binds them to `m`, `n`, and `p`,
and returns evidence for the corresponding instance of the equation.

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially.  Reading the chain of equations in the base case of the proof,
the top and bottom of the chain match the two sides of the equation to
be shown, and reading down from the top and up from the bottom takes us to
`n + p` in the middle.  No justification other than simplification is required.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    (m + n) + p ≡ m + (n + p)

Reading the chain of equations in the inductive case of the proof, the
top and bottom of the chain match the two sides of the equation to be
shown, and reading down from the top and up from the bottom takes us
to the simplified equation above. The remaining equation, does not follow
from simplification alone, so we use an additional operator for chain
reasoning, `_≡⟨_⟩_`, where a justification for the equation appears
within angle brackets.  The justification given is:

    ⟨ cong suc (+-assoc m n p) ⟩

Here, the recursive invocation `+-assoc m n p` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.

A relation is said to be a *congruence* for a given function if it is
preserved by applying that function.  If `e` is evidence that `x ≡ y`,
then `cong f e` is evidence that `f x ≡ f y`, for any function `f`.

Here the inductive hypothesis is not assumed, but instead proved by a
recursive invocation of the function we are defining, `+-assoc m n p`.
As with addition, this is well founded because associativity of
larger numbers is proved in terms of associativity of smaller numbers.
In this case, `assoc (suc m) n p` is proved using `assoc m n p`.
The correspondence between proof by induction and definition by
recursion is one of the most appealing aspects of Agda.


## Our second proof: commutativity

Another important property of addition is that it is *commutative*, that is,
that the order of the operands does not matter:

    m + n ≡ n + m

The proof requires that we first demonstrate two lemmas.

### The first lemma

The base case of the definition of addition states that zero
is a left-identity:

    zero + n ≡ n

Our first lemma states that zero is also a right-identity:

    m + zero ≡ m

Here is the lemma's statement and proof.
<pre class="Agda">{% raw %}<a id="+-identityʳ"></a><a id="9317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#9317" class="Function">+-identityʳ</a> <a id="9329" class="Symbol">:</a> <a id="9331" class="Symbol">∀</a> <a id="9333" class="Symbol">(</a><a id="9334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#9334" class="Bound">m</a> <a id="9336" class="Symbol">:</a> <a id="9338" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="9339" class="Symbol">)</a> <a id="9341" class="Symbol">→</a> <a id="9343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#9334" class="Bound">m</a> <a id="9345" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="9347" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="9352" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="9354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#9334" class="Bound">m</a>
<a id="9356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#9317" class="Function">+-identityʳ</a> <a id="9368" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="9373" class="Symbol">=</a>
  <a id="9377" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="9387" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="9392" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="9394" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="9401" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="9409" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="9416" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>
<a id="9418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#9317" class="Function">+-identityʳ</a> <a id="9430" class="Symbol">(</a><a id="9431" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#9435" class="Bound">m</a><a id="9436" class="Symbol">)</a> <a id="9438" class="Symbol">=</a>
  <a id="9442" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="9452" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#9435" class="Bound">m</a> <a id="9458" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="9460" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="9467" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="9475" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9479" class="Symbol">(</a><a id="9480" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#9435" class="Bound">m</a> <a id="9482" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="9484" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="9488" class="Symbol">)</a>
  <a id="9492" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="9495" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a> <a id="9500" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9504" class="Symbol">(</a><a id="9505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#9317" class="Function">+-identityʳ</a> <a id="9517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#9435" class="Bound">m</a><a id="9518" class="Symbol">)</a> <a id="9520" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="9526" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#9435" class="Bound">m</a>
  <a id="9534" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>{% endraw %}</pre>
The signature states that we are defining the identifier `+-identityʳ` which
provides evidence for the proposition:

    ∀ (m : ℕ) → m + zero ≡ m

Evidence for the proposition is a function that accepts a natural
number, binds it to `m`, and returns evidence for the corresponding
instance of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + zero ≡ zero

Simplifying with the base case of addition, this is straightforward.

For the inductive case, we must show:

    (suc m) + zero = suc m

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + zero) = suc m

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + zero ≡ m

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation above.  The remaining
equation has the justification:

    ⟨ cong suc (+-identityʳ m) ⟩

Here, the recursive invocation `+-identityʳ m` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the first lemma.

### The second lemma

The inductive case of the definition of addition pushes `suc` on the
first argument to the outside:

    suc m + n ≡ suc (m + n)

Our second lemma does the same for `suc` on the second argument:

    m + suc n ≡ suc (m + n)

Here is the lemma's statement and proof.
<pre class="Agda">{% raw %}<a id="+-suc"></a><a id="10990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#10990" class="Function">+-suc</a> <a id="10996" class="Symbol">:</a> <a id="10998" class="Symbol">∀</a> <a id="11000" class="Symbol">(</a><a id="11001" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11001" class="Bound">m</a> <a id="11003" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11003" class="Bound">n</a> <a id="11005" class="Symbol">:</a> <a id="11007" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11008" class="Symbol">)</a> <a id="11010" class="Symbol">→</a> <a id="11012" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11001" class="Bound">m</a> <a id="11014" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11016" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11003" class="Bound">n</a> <a id="11022" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="11024" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11028" class="Symbol">(</a><a id="11029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11001" class="Bound">m</a> <a id="11031" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11003" class="Bound">n</a><a id="11034" class="Symbol">)</a>
<a id="11036" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#10990" class="Function">+-suc</a> <a id="11042" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="11047" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11047" class="Bound">n</a> <a id="11049" class="Symbol">=</a>
  <a id="11053" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="11063" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="11068" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11070" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11047" class="Bound">n</a>
  <a id="11078" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="11086" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11090" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11047" class="Bound">n</a>
  <a id="11094" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="11102" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11106" class="Symbol">(</a><a id="11107" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="11112" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11047" class="Bound">n</a><a id="11115" class="Symbol">)</a>
  <a id="11119" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>
<a id="11121" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#10990" class="Function">+-suc</a> <a id="11127" class="Symbol">(</a><a id="11128" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11132" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11132" class="Bound">m</a><a id="11133" class="Symbol">)</a> <a id="11135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11135" class="Bound">n</a> <a id="11137" class="Symbol">=</a>
  <a id="11141" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="11151" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11155" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11132" class="Bound">m</a> <a id="11157" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11159" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11135" class="Bound">n</a>
  <a id="11167" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="11175" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11179" class="Symbol">(</a><a id="11180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11132" class="Bound">m</a> <a id="11182" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11184" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11135" class="Bound">n</a><a id="11189" class="Symbol">)</a>
  <a id="11193" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="11196" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a> <a id="11201" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11205" class="Symbol">(</a><a id="11206" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#10990" class="Function">+-suc</a> <a id="11212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11132" class="Bound">m</a> <a id="11214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11135" class="Bound">n</a><a id="11215" class="Symbol">)</a> <a id="11217" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="11223" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11227" class="Symbol">(</a><a id="11228" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11232" class="Symbol">(</a><a id="11233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11132" class="Bound">m</a> <a id="11235" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11237" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11135" class="Bound">n</a><a id="11238" class="Symbol">))</a>
  <a id="11243" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="11251" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11255" class="Symbol">(</a><a id="11256" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11132" class="Bound">m</a> <a id="11262" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#11135" class="Bound">n</a><a id="11265" class="Symbol">)</a>
  <a id="11269" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>{% endraw %}</pre>
The signature states that we are defining the identifier `+-suc` which provides
evidence for the proposition:

    ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

Evidence for the proposition is a function that accepts two natural numbers,
binds them to `m` and `n`, and returns evidence for the corresponding instance
of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + suc n ≡ suc (zero + n)

Simplifying with the base case of addition, this is straightforward.

For the inductive case, we must show:

    suc m + suc n ≡ suc (suc m + n)

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + suc n) ≡ suc (suc (m + n))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + suc n ≡ suc (m + n)

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation in the middle.  The remaining
equation has the justification:

    ⟨ cong suc (+-suc m n) ⟩

Here, the recursive invocation `+-suc m n` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the second lemma.

### The proposition

Finally, here is our proposition's statement and proof.
<pre class="Agda">{% raw %}<a id="+-comm"></a><a id="12579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12579" class="Function">+-comm</a> <a id="12586" class="Symbol">:</a> <a id="12588" class="Symbol">∀</a> <a id="12590" class="Symbol">(</a><a id="12591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12591" class="Bound">m</a> <a id="12593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12593" class="Bound">n</a> <a id="12595" class="Symbol">:</a> <a id="12597" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="12598" class="Symbol">)</a> <a id="12600" class="Symbol">→</a> <a id="12602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12591" class="Bound">m</a> <a id="12604" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12593" class="Bound">n</a> <a id="12608" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="12610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12593" class="Bound">n</a> <a id="12612" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12591" class="Bound">m</a>
<a id="12616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12579" class="Function">+-comm</a> <a id="12623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12623" class="Bound">m</a> <a id="12625" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="12630" class="Symbol">=</a>
  <a id="12634" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="12644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12623" class="Bound">m</a> <a id="12646" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12648" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="12655" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="12658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#9317" class="Function">+-identityʳ</a> <a id="12670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12623" class="Bound">m</a> <a id="12672" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="12678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12623" class="Bound">m</a>
  <a id="12682" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="12690" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="12695" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12697" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12623" class="Bound">m</a>
  <a id="12701" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>
<a id="12703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12579" class="Function">+-comm</a> <a id="12710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12710" class="Bound">m</a> <a id="12712" class="Symbol">(</a><a id="12713" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12717" class="Bound">n</a><a id="12718" class="Symbol">)</a> <a id="12720" class="Symbol">=</a>
  <a id="12724" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3962" class="Function Operator">begin</a>
    <a id="12734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12710" class="Bound">m</a> <a id="12736" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12738" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12717" class="Bound">n</a>
  <a id="12746" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="12749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#10990" class="Function">+-suc</a> <a id="12755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12710" class="Bound">m</a> <a id="12757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12717" class="Bound">n</a> <a id="12759" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="12765" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12769" class="Symbol">(</a><a id="12770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12710" class="Bound">m</a> <a id="12772" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12717" class="Bound">n</a><a id="12775" class="Symbol">)</a>
  <a id="12779" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">≡⟨</a> <a id="12782" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a> <a id="12787" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12791" class="Symbol">(</a><a id="12792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12579" class="Function">+-comm</a> <a id="12799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12710" class="Bound">m</a> <a id="12801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12717" class="Bound">n</a><a id="12802" class="Symbol">)</a> <a id="12804" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4079" class="Function Operator">⟩</a>
    <a id="12810" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12814" class="Symbol">(</a><a id="12815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12717" class="Bound">n</a> <a id="12817" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12819" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12710" class="Bound">m</a><a id="12820" class="Symbol">)</a>
  <a id="12824" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4020" class="Function Operator">≡⟨⟩</a>
    <a id="12832" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12717" class="Bound">n</a> <a id="12838" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12840" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#12710" class="Bound">m</a>
  <a id="12844" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4260" class="Function Operator">∎</a>{% endraw %}</pre>
The first line states that we are defining the identifier
`+-comm` which provides evidence for the proposition:

    ∀ (m n : ℕ) → m + n ≡ n + m

Evidence for the proposition is a function that accepts two
natural numbers, binds them to `m` and `n`, and returns evidence for the
corresponding instance of the equation.  The proof is by
induction on `n`.  (Not on `m` this time!)

For the base case, we must show:

    m + zero ≡ zero + m

Simplifying both sides with the base case of addition yields the equation:

    m + zero ≡ m

The the remaining equation has the justification

    ⟨ +-identityʳ m ⟩

which invokes the first lemma.

For the inductive case, we must show:

    m + suc n ≡ suc n + m

Simplifying both sides with the inductive case of addition yields the equation:

    m + suc n ≡ suc (n + m)

We show this in two steps.  First, we have:

    m + suc n ≡ suc (m + n)

which is justified by the second lemma, `⟨ +-suc m n ⟩`.  Then we
have

    suc (m + n) ≡ suc (n + m)

which is justified by congruence and the induction hypothesis,
`⟨ cong suc (+-comm m n) ⟩`.  This completes the proposition.

Agda requires that identifiers are defined before they are used,
so we must present the lemmas before the main proposition, as we
have done above.  In practice, one will often attempt to prove
the main proposition first, and the equations required to do so
will suggest what lemmas to prove.



## Creation, one last time

Returning to the proof of associativity, it may be helpful to view the inductive
proof (or, equivalently, the recursive definition) as a creation story.  This
time we are concerned with judgements asserting associativity.

     -- in the beginning, we know nothing about associativity

Now, we apply the rules to all the judgements we know about.  The base
case tells us that `(zero + n) + p ≡ zero + (n + p)` for every natural
`n` and `p`.  The inductive case tells us that if `(m + n) + p ≡ m +
(n + p)` (on the day before today) then
`(suc m + n) + p ≡ suc m + (n + p)` (today).
We didn't know any judgments about associativity before today, so that
rule doesn't give us any new judgments.

    -- on the first day, we know about associativity of 0
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...

Then we repeat the process, so on the next day we know about all the
judgements from the day before, plus any judgements added by the rules.
The base case tells us nothing new, but now the inductive case adds
more judgements.

    -- on the second day, we know about associativity of 0 and 1
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...

And we repeat the process again.

    -- on the third day, we know about associativity of 0, 1, and 2
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...

You've got the hang of it by now.

    -- on the fourth day, we know about associativity of 0, 1, 2, and 3
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
    (3 + 0) + 0 ≡ 3 + (0 + 0)   ...   (3 + 4) + 5 ≡ 3 + (4 + 5)   ...

The process continues.  On the *m*th day we will know all the
judgements where the first number is less than *m*.

There is also a completely finite approach to generating the same equations,
which is left as an exercise for the reader.

### Exercise (`+-assoc-finite`)

Write out what is known about associativity on each of the first four
days using a finite story of creation, as
[earlier]({{ site.baseurl }}{% link out/plfa/Naturals.md %}#finite-creation).


## Associativity with rewrite

There is more than one way to skin a cat.  Here is a second proof of
associativity of addition in Agda, using `rewrite` rather than chains of
equations.
<pre class="Agda">{% raw %}<a id="+-assoc′"></a><a id="16914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16914" class="Function">+-assoc′</a> <a id="16923" class="Symbol">:</a> <a id="16925" class="Symbol">∀</a> <a id="16927" class="Symbol">(</a><a id="16928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16928" class="Bound">m</a> <a id="16930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16930" class="Bound">n</a> <a id="16932" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16932" class="Bound">p</a> <a id="16934" class="Symbol">:</a> <a id="16936" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16937" class="Symbol">)</a> <a id="16939" class="Symbol">→</a> <a id="16941" class="Symbol">(</a><a id="16942" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16928" class="Bound">m</a> <a id="16944" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16930" class="Bound">n</a><a id="16947" class="Symbol">)</a> <a id="16949" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16932" class="Bound">p</a> <a id="16953" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="16955" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16928" class="Bound">m</a> <a id="16957" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16959" class="Symbol">(</a><a id="16960" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16930" class="Bound">n</a> <a id="16962" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16932" class="Bound">p</a><a id="16965" class="Symbol">)</a>
<a id="16967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16914" class="Function">+-assoc′</a> <a id="16976" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="16981" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16981" class="Bound">n</a> <a id="16983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16983" class="Bound">p</a> <a id="16985" class="Symbol">=</a> <a id="16987" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="16992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16914" class="Function">+-assoc′</a> <a id="17001" class="Symbol">(</a><a id="17002" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#17006" class="Bound">m</a><a id="17007" class="Symbol">)</a> <a id="17009" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#17009" class="Bound">n</a> <a id="17011" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#17011" class="Bound">p</a> <a id="17013" class="Keyword">rewrite</a> <a id="17021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#16914" class="Function">+-assoc′</a> <a id="17030" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#17006" class="Bound">m</a> <a id="17032" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#17009" class="Bound">n</a> <a id="17034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#17011" class="Bound">p</a> <a id="17036" class="Symbol">=</a> <a id="17038" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially. The proof that a term is equal to itself is written `refl`.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

After rewriting with the inductive hypothesis these two terms are equal, and the
proof is again given by `refl`.  Rewriting by a given equation is indicated by
the keyword `rewrite` followed by a proof of that equation.  Rewriting avoids
not only chains of equations but also the need to invoke `cong`.


## Commutativity with rewrite

Here is a second proof of commutativity of addition, using `rewrite` rather than
chains of equations.
<pre class="Agda">{% raw %}<a id="+-identity′"></a><a id="17957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#17957" class="Function">+-identity′</a> <a id="17969" class="Symbol">:</a> <a id="17971" class="Symbol">∀</a> <a id="17973" class="Symbol">(</a><a id="17974" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#17974" class="Bound">n</a> <a id="17976" class="Symbol">:</a> <a id="17978" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17979" class="Symbol">)</a> <a id="17981" class="Symbol">→</a> <a id="17983" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#17974" class="Bound">n</a> <a id="17985" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17987" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="17992" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="17994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#17974" class="Bound">n</a>
<a id="17996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#17957" class="Function">+-identity′</a> <a id="18008" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="18013" class="Symbol">=</a> <a id="18015" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="18020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#17957" class="Function">+-identity′</a> <a id="18032" class="Symbol">(</a><a id="18033" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18037" class="Bound">n</a><a id="18038" class="Symbol">)</a> <a id="18040" class="Keyword">rewrite</a> <a id="18048" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#17957" class="Function">+-identity′</a> <a id="18060" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18037" class="Bound">n</a> <a id="18062" class="Symbol">=</a> <a id="18064" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="+-suc′"></a><a id="18070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18070" class="Function">+-suc′</a> <a id="18077" class="Symbol">:</a> <a id="18079" class="Symbol">∀</a> <a id="18081" class="Symbol">(</a><a id="18082" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18082" class="Bound">m</a> <a id="18084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18084" class="Bound">n</a> <a id="18086" class="Symbol">:</a> <a id="18088" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="18089" class="Symbol">)</a> <a id="18091" class="Symbol">→</a> <a id="18093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18082" class="Bound">m</a> <a id="18095" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18097" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18084" class="Bound">n</a> <a id="18103" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="18105" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18109" class="Symbol">(</a><a id="18110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18082" class="Bound">m</a> <a id="18112" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18084" class="Bound">n</a><a id="18115" class="Symbol">)</a>
<a id="18117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18070" class="Function">+-suc′</a> <a id="18124" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="18129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18129" class="Bound">n</a> <a id="18131" class="Symbol">=</a> <a id="18133" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="18138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18070" class="Function">+-suc′</a> <a id="18145" class="Symbol">(</a><a id="18146" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18150" class="Bound">m</a><a id="18151" class="Symbol">)</a> <a id="18153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18153" class="Bound">n</a> <a id="18155" class="Keyword">rewrite</a> <a id="18163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18070" class="Function">+-suc′</a> <a id="18170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18150" class="Bound">m</a> <a id="18172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18153" class="Bound">n</a> <a id="18174" class="Symbol">=</a> <a id="18176" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="+-comm′"></a><a id="18182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18182" class="Function">+-comm′</a> <a id="18190" class="Symbol">:</a> <a id="18192" class="Symbol">∀</a> <a id="18194" class="Symbol">(</a><a id="18195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18195" class="Bound">m</a> <a id="18197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18197" class="Bound">n</a> <a id="18199" class="Symbol">:</a> <a id="18201" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="18202" class="Symbol">)</a> <a id="18204" class="Symbol">→</a> <a id="18206" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18195" class="Bound">m</a> <a id="18208" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18210" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18197" class="Bound">n</a> <a id="18212" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="18214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18197" class="Bound">n</a> <a id="18216" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18195" class="Bound">m</a>
<a id="18220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18182" class="Function">+-comm′</a> <a id="18228" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18228" class="Bound">m</a> <a id="18230" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="18235" class="Keyword">rewrite</a> <a id="18243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#17957" class="Function">+-identity′</a> <a id="18255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18228" class="Bound">m</a> <a id="18257" class="Symbol">=</a> <a id="18259" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="18264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18182" class="Function">+-comm′</a> <a id="18272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18272" class="Bound">m</a> <a id="18274" class="Symbol">(</a><a id="18275" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18279" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18279" class="Bound">n</a><a id="18280" class="Symbol">)</a> <a id="18282" class="Keyword">rewrite</a> <a id="18290" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18070" class="Function">+-suc′</a> <a id="18297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18272" class="Bound">m</a> <a id="18299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18279" class="Bound">n</a> <a id="18301" class="Symbol">|</a> <a id="18303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18182" class="Function">+-comm′</a> <a id="18311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18272" class="Bound">m</a> <a id="18313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Induction.md %}{% raw %}#18279" class="Bound">n</a> <a id="18315" class="Symbol">=</a> <a id="18317" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>
In the final line, rewriting with two equations is
indicated by separating the two proofs of the relevant equations by a
vertical bar; the rewrite on the left is performed before that on the
right.


## Building proofs interactively

It is instructive to see how to build the alternative proof of
associativity using the interactive features of Agda in Emacs.
Begin by typing

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = ?

The question mark indicates that you would like Agda to help with
filling in that part of the code.  If you type `C-c C-l` (control-c
followed by control-l), the question mark will be replaced.

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = { }0

The empty braces are called a *hole*, and 0 is a number used for
referring to the hole.  The hole may display highlighted in green.
Emacs will also create a new window at the bottom of the screen
displaying the text

    ?0 : ((m + n) + p) ≡ (m + (n + p))

This indicates that hole 0 is to be filled in with a proof of
the stated judgement.

We wish to prove the proposition by induction on `m`.  Move
the cursor into the hole and type `C-c C-c`.  You will be given
the prompt:

    pattern variables to case (empty for split on result):

Typing `m` will cause a split on that variable, resulting
in an update to the code.

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = { }0
    +-assoc′ (suc m) n p = { }1

There are now two holes, and the window at the bottom tells you what
each is required to prove:

    ?0 : ((zero + n) + p) ≡ (zero + (n + p))
    ?1 : ((suc m + n) + p) ≡ (suc m + (n + p))

Going into hole 0 and typing `C-c C-,` will display the text:

    Goal: (n + p) ≡ (n + p)
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ

This indicates that after simplification the goal for hole 0 is as
stated, and that variables `p` and `n` of the stated types are
available to use in the proof.  The proof of the given goal is
trivial, and going into the goal and typing `C-c C-r` will fill it in,
renumbering the remaining hole to 0:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p = { }0

Going into the new hole 0 and typing `C-c C-,` will display the text:

    Goal: suc ((m + n) + p) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

Again, this gives the simplified goal and the available variables.
In this case, we need to rewrite by the induction
hypothesis, so let's edit the text accordingly:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = { }0

Going into the remaining hole and typing `C-c C-,` will display the text:

    Goal: suc (m + (n + p)) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

The proof of the given goal is trivial, and going into the goal and
typing `C-c C-r` will fill it in, completing the proof:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


### Exercise (`+-swap`)

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.  You may need to use
the following function from the standard library:

    sym : ∀ {m n : ℕ} → m ≡ n → n ≡ m

### Exercise (`*-distrib-+`)

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

### Exercise (`*-assoc`)

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

### Exercise (`*-comm`)

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

### Exercise (`0∸n≡0`)

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

### Exercise (`∸-+-assoc`)

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

## Standard library

Definitions similar to those in this chapter can be found in the standard library.
<pre class="Agda">{% raw %}<a id="22807" class="Keyword">import</a> <a id="22814" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="22834" class="Keyword">using</a> <a id="22840" class="Symbol">(</a><a id="22841" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7782" class="Function">+-assoc</a><a id="22848" class="Symbol">;</a> <a id="22850" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7938" class="Function">+-identityʳ</a><a id="22861" class="Symbol">;</a> <a id="22863" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7679" class="Function">+-suc</a><a id="22868" class="Symbol">;</a> <a id="22870" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8115" class="Function">+-comm</a><a id="22876" class="Symbol">)</a>{% endraw %}</pre>

## Unicode

This chapter uses the following unicode.

    ∀  U+2200  FOR ALL (\forall)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')

Similar to `\r`, the command `\^r` gives access to a variety of
superscript rightward arrows, and also a superscript letter `r`.
The command `\'` gives access to a range of primes (`′ ″ ‴ ⁗`).

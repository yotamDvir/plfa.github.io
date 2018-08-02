---
title     : "Negation: Negation, with intuitionistic and classical logic"
layout    : page
permalink : /Negation/
---

<pre class="Agda">{% raw %}<a id="137" class="Keyword">module</a> <a id="144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}" class="Module">plfa.Negation</a> <a id="158" class="Keyword">where</a>{% endraw %}</pre>

This chapter introduces negation, and discusses intuitionistic
and classical logic.

## Imports

<pre class="Agda">{% raw %}<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="336" class="Keyword">using</a> <a id="342" class="Symbol">(</a><a id="343" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="346" class="Symbol">;</a> <a id="348" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="352" class="Symbol">)</a>
<a id="354" class="Keyword">open</a> <a id="359" class="Keyword">import</a> <a id="366" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="375" class="Keyword">using</a> <a id="381" class="Symbol">(</a><a id="382" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="383" class="Symbol">;</a> <a id="385" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="389" class="Symbol">;</a> <a id="391" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="394" class="Symbol">)</a>
<a id="396" class="Keyword">open</a> <a id="401" class="Keyword">import</a> <a id="408" href="https://agda.github.io/agda-stdlib/Data.Empty.html" class="Module">Data.Empty</a> <a id="419" class="Keyword">using</a> <a id="425" class="Symbol">(</a><a id="426" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a><a id="427" class="Symbol">;</a> <a id="429" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function">⊥-elim</a><a id="435" class="Symbol">)</a>
<a id="437" class="Keyword">open</a> <a id="442" class="Keyword">import</a> <a id="449" href="https://agda.github.io/agda-stdlib/Data.Sum.html" class="Module">Data.Sum</a> <a id="458" class="Keyword">using</a> <a id="464" class="Symbol">(</a><a id="465" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#414" class="Datatype Operator">_⊎_</a><a id="468" class="Symbol">;</a> <a id="470" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#470" class="InductiveConstructor">inj₁</a><a id="474" class="Symbol">;</a> <a id="476" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#495" class="InductiveConstructor">inj₂</a><a id="480" class="Symbol">)</a>
<a id="482" class="Keyword">open</a> <a id="487" class="Keyword">import</a> <a id="494" href="https://agda.github.io/agda-stdlib/Data.Product.html" class="Module">Data.Product</a> <a id="507" class="Keyword">using</a> <a id="513" class="Symbol">(</a><a id="514" href="https://agda.github.io/agda-stdlib/Data.Product.html#1329" class="Function Operator">_×_</a><a id="517" class="Symbol">;</a> <a id="519" href="https://agda.github.io/agda-stdlib/Data.Product.html#559" class="Field">proj₁</a><a id="524" class="Symbol">;</a> <a id="526" href="https://agda.github.io/agda-stdlib/Data.Product.html#573" class="Field">proj₂</a><a id="531" class="Symbol">)</a> <a id="533" class="Keyword">renaming</a> <a id="542" class="Symbol">(</a><a id="543" href="https://agda.github.io/agda-stdlib/Data.Product.html#543" class="InductiveConstructor Operator">_,_</a> <a id="547" class="Symbol">to</a> <a id="550" href="https://agda.github.io/agda-stdlib/Data.Product.html#543" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="555" class="Symbol">)</a>
<a id="557" class="Keyword">open</a> <a id="562" class="Keyword">import</a> <a id="569" href="https://agda.github.io/agda-stdlib/Function.html" class="Module">Function</a> <a id="578" class="Keyword">using</a> <a id="584" class="Symbol">(</a><a id="585" href="https://agda.github.io/agda-stdlib/Function.html#759" class="Function Operator">_∘_</a><a id="588" class="Symbol">)</a>
<a id="590" class="Keyword">open</a> <a id="595" class="Keyword">import</a> <a id="602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}" class="Module">plfa.Isomorphism</a> <a id="619" class="Keyword">using</a> <a id="625" class="Symbol">(</a><a id="626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4104" class="Record Operator">_≃_</a><a id="629" class="Symbol">;</a> <a id="631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#6789" class="Function">≃-sym</a><a id="636" class="Symbol">;</a> <a id="638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#7115" class="Function">≃-trans</a><a id="645" class="Symbol">;</a> <a id="647" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#8909" class="Record Operator">_≲_</a><a id="650" class="Symbol">)</a>{% endraw %}</pre>


## Negation

Given a proposition `A`, the negation `¬ A` holds if `A` cannot hold.
We formalise this idea by declaring negation to be the same
as implication of false.
<pre class="Agda">{% raw %}<a id="¬_"></a><a id="846" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬_</a> <a id="849" class="Symbol">:</a> <a id="851" class="PrimitiveType">Set</a> <a id="855" class="Symbol">→</a> <a id="857" class="PrimitiveType">Set</a>
<a id="861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#863" class="Bound">A</a> <a id="865" class="Symbol">=</a> <a id="867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#863" class="Bound">A</a> <a id="869" class="Symbol">→</a> <a id="871" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a>{% endraw %}</pre>
This is a form of *proof by contradiction*: if assuming `A` leads
to the conclusion `⊥` (a contradiction), then we must have `¬ A`.

Evidence that `¬ A` holds is of the form

    λ{ x → N }

where `N` is a term of type `⊥` containing as a free variable `x` of type `A`.
In other words, evidence that `¬ A` holds is a function that converts evidence
that `A` holds into evidence that `⊥` holds.

Given evidence that both `¬ A` and `A` hold, we can conclude that `⊥` holds.
In other words, if both `¬ A` and `A` hold, then we have a contradiction.
<pre class="Agda">{% raw %}<a id="¬-elim"></a><a id="1443" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1443" class="Function">¬-elim</a> <a id="1450" class="Symbol">:</a> <a id="1452" class="Symbol">∀</a> <a id="1454" class="Symbol">{</a><a id="1455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1455" class="Bound">A</a> <a id="1457" class="Symbol">:</a> <a id="1459" class="PrimitiveType">Set</a><a id="1462" class="Symbol">}</a> <a id="1464" class="Symbol">→</a> <a id="1466" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="1468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1455" class="Bound">A</a> <a id="1470" class="Symbol">→</a> <a id="1472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1455" class="Bound">A</a> <a id="1474" class="Symbol">→</a> <a id="1476" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a>
<a id="1478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1443" class="Function">¬-elim</a> <a id="1485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1485" class="Bound">¬x</a> <a id="1488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1488" class="Bound">x</a> <a id="1490" class="Symbol">=</a> <a id="1492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1485" class="Bound">¬x</a> <a id="1495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#1488" class="Bound">x</a>{% endraw %}</pre>
Here we write `¬x` for evidence of `¬ A` and `x` for evidence of `A`.  This
means that `¬x` must be a function of type `A → ⊥`, and hence the application
`¬x x` must be of type `⊥`.  Note that this rule is just a special case of `→-elim`.

We set the precedence of negation so that it binds more tightly
than disjunction and conjunction, but less tightly than anything else.
<pre class="Agda">{% raw %}<a id="1896" class="Keyword">infix</a> <a id="1902" class="Number">3</a> <a id="1904" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬_</a>{% endraw %}</pre>
Thus, `¬ A × ¬ B` parses as `(¬ A) × (¬ B)` and `¬ m ≡ n` as `¬ (m ≡ n)`.

In *classical* logic, we have that `A` is equivalent to `¬ ¬ A`.
As we discuss below, in Agda we use *intuitionistic* logic, where
we have only half of this equivalence, namely that `A` implies `¬ ¬ A`.
<pre class="Agda">{% raw %}<a id="¬¬-intro"></a><a id="2209" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2209" class="Function">¬¬-intro</a> <a id="2218" class="Symbol">:</a> <a id="2220" class="Symbol">∀</a> <a id="2222" class="Symbol">{</a><a id="2223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2223" class="Bound">A</a> <a id="2225" class="Symbol">:</a> <a id="2227" class="PrimitiveType">Set</a><a id="2230" class="Symbol">}</a> <a id="2232" class="Symbol">→</a> <a id="2234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2223" class="Bound">A</a> <a id="2236" class="Symbol">→</a> <a id="2238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="2240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="2242" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2223" class="Bound">A</a>
<a id="2244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2209" class="Function">¬¬-intro</a> <a id="2253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2253" class="Bound">x</a> <a id="2255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2255" class="Bound">¬x</a> <a id="2258" class="Symbol">=</a> <a id="2260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2255" class="Bound">¬x</a> <a id="2263" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2253" class="Bound">x</a>{% endraw %}</pre>
Let `x` be evidence of `A`. We will show that assuming
`¬ A` leads to a contradiction, and hence `¬ ¬ A` must hold.
Let `¬x` be evidence of `¬ A`.  Then from `A` and `¬ A`
we have a contradiction, evidenced by `¬x x`.  Hence, we have
shown `¬ ¬ A`.

We cannot show that `¬ ¬ A` implies `A`, but we can show that
`¬ ¬ ¬ A` implies `¬ A`.
<pre class="Agda">{% raw %}<a id="¬¬¬-elim"></a><a id="2626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2626" class="Function">¬¬¬-elim</a> <a id="2635" class="Symbol">:</a> <a id="2637" class="Symbol">∀</a> <a id="2639" class="Symbol">{</a><a id="2640" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2640" class="Bound">A</a> <a id="2642" class="Symbol">:</a> <a id="2644" class="PrimitiveType">Set</a><a id="2647" class="Symbol">}</a> <a id="2649" class="Symbol">→</a> <a id="2651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="2653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="2655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="2657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2640" class="Bound">A</a> <a id="2659" class="Symbol">→</a> <a id="2661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="2663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2640" class="Bound">A</a>
<a id="2665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2626" class="Function">¬¬¬-elim</a> <a id="2674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2674" class="Bound">¬¬¬x</a> <a id="2679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2679" class="Bound">x</a> <a id="2681" class="Symbol">=</a> <a id="2683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2674" class="Bound">¬¬¬x</a> <a id="2688" class="Symbol">(</a><a id="2689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2209" class="Function">¬¬-intro</a> <a id="2698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#2679" class="Bound">x</a><a id="2699" class="Symbol">)</a>{% endraw %}</pre>
Let `¬¬¬x` be evidence of `¬ ¬ ¬ A`. We will show that assuming
`A` leads to a contradiction, and hence `¬ A` must hold.
Let `x` be evidence of `A`. Then by the previous result, we
can conclude `¬ ¬ A`, evidenced by `¬¬-intro x`.  Then from
`¬ ¬ ¬ A` and `¬ ¬ A` we have a contradiction, evidenced by
`¬¬¬x (¬¬-intro x)`.  Hence we have shown `¬ A`.

Another law of logic is *contraposition*,
stating that if `A` implies `B`, then `¬ B` implies `¬ A`.
<pre class="Agda">{% raw %}<a id="contraposition"></a><a id="3177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3177" class="Function">contraposition</a> <a id="3192" class="Symbol">:</a> <a id="3194" class="Symbol">∀</a> <a id="3196" class="Symbol">{</a><a id="3197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3197" class="Bound">A</a> <a id="3199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3199" class="Bound">B</a> <a id="3201" class="Symbol">:</a> <a id="3203" class="PrimitiveType">Set</a><a id="3206" class="Symbol">}</a> <a id="3208" class="Symbol">→</a> <a id="3210" class="Symbol">(</a><a id="3211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3197" class="Bound">A</a> <a id="3213" class="Symbol">→</a> <a id="3215" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3199" class="Bound">B</a><a id="3216" class="Symbol">)</a> <a id="3218" class="Symbol">→</a> <a id="3220" class="Symbol">(</a><a id="3221" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="3223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3199" class="Bound">B</a> <a id="3225" class="Symbol">→</a> <a id="3227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="3229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3197" class="Bound">A</a><a id="3230" class="Symbol">)</a>
<a id="3232" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3177" class="Function">contraposition</a> <a id="3247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3247" class="Bound">f</a> <a id="3249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3249" class="Bound">¬y</a> <a id="3252" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3252" class="Bound">x</a> <a id="3254" class="Symbol">=</a> <a id="3256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3249" class="Bound">¬y</a> <a id="3259" class="Symbol">(</a><a id="3260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3247" class="Bound">f</a> <a id="3262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3252" class="Bound">x</a><a id="3263" class="Symbol">)</a>{% endraw %}</pre>
Let `f` be evidence of `A → B` and let `¬y` be evidence of `¬ B`.  We
will show that assuming `A` leads to a contradiction, and hence
`¬ A` must hold. Let `x` be evidence of `A`.  Then from `A → B` and
`A` we may conclude `B`, evidenced by `f x`, and from `B` and `¬ B`
we may conclude `⊥`, evidenced by `¬y (f x)`.  Hence, we have shown
`¬ A`.

Using negation, it is straightforward to define inequality.
<pre class="Agda">{% raw %}<a id="_≢_"></a><a id="3695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3695" class="Function Operator">_≢_</a> <a id="3699" class="Symbol">:</a> <a id="3701" class="Symbol">∀</a> <a id="3703" class="Symbol">{</a><a id="3704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3704" class="Bound">A</a> <a id="3706" class="Symbol">:</a> <a id="3708" class="PrimitiveType">Set</a><a id="3711" class="Symbol">}</a> <a id="3713" class="Symbol">→</a> <a id="3715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3704" class="Bound">A</a> <a id="3717" class="Symbol">→</a> <a id="3719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3704" class="Bound">A</a> <a id="3721" class="Symbol">→</a> <a id="3723" class="PrimitiveType">Set</a>
<a id="3727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3727" class="Bound">x</a> <a id="3729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3695" class="Function Operator">≢</a> <a id="3731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3731" class="Bound">y</a>  <a id="3734" class="Symbol">=</a>  <a id="3737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="3739" class="Symbol">(</a><a id="3740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3727" class="Bound">x</a> <a id="3742" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="3744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3731" class="Bound">y</a><a id="3745" class="Symbol">)</a>{% endraw %}</pre>
It is straightforward to show distinct numbers are not equal.
<pre class="Agda">{% raw %}<a id="3833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3833" class="Function">_</a> <a id="3835" class="Symbol">:</a> <a id="3837" class="Number">1</a> <a id="3839" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3695" class="Function Operator">≢</a> <a id="3841" class="Number">2</a>
<a id="3843" class="Symbol">_</a> <a id="3845" class="Symbol">=</a> <a id="3847" class="Symbol">λ()</a>{% endraw %}</pre>
This is our first use of an absurd pattern in a lambda expression.
The type `M ≡ N` is occupied exactly when `M` and `N` simplify to
identical terms. Since `1` and `2` simplify to distinct normal forms,
Agda determines that there is no possible evidence that `1 ≡ 2`.
As a second example, it is also easy to validate
Peano's postulate that zero is not the successor of any number.
<pre class="Agda">{% raw %}<a id="peano"></a><a id="4256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4256" class="Function">peano</a> <a id="4262" class="Symbol">:</a> <a id="4264" class="Symbol">∀</a> <a id="4266" class="Symbol">{</a><a id="4267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4267" class="Bound">m</a> <a id="4269" class="Symbol">:</a> <a id="4271" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="4272" class="Symbol">}</a> <a id="4274" class="Symbol">→</a> <a id="4276" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="4281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#3695" class="Function Operator">≢</a> <a id="4283" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="4287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4267" class="Bound">m</a>
<a id="4289" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4256" class="Function">peano</a> <a id="4295" class="Symbol">=</a> <a id="4297" class="Symbol">λ()</a>{% endraw %}</pre>
The evidence is essentially the same, as the absurd pattern matches
all possible evidence of type `zero ≡ suc m`.

Given the correspondence of implication to exponentiation and
false to the type with no members, we can view negation as
raising to the zero power.  This indeed corresponds to what
we know for arithmetic, where

    0 ^ n  =  1,  if n = 0
           =  0,  if n ≠ 0

Indeed, there is exactly one proof of `⊥ → ⊥`.
<pre class="Agda">{% raw %}<a id="id"></a><a id="4754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4754" class="Function">id</a> <a id="4757" class="Symbol">:</a> <a id="4759" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a> <a id="4761" class="Symbol">→</a> <a id="4763" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a>
<a id="4765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4754" class="Function">id</a> <a id="4768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4768" class="Bound">x</a> <a id="4770" class="Symbol">=</a> <a id="4772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#4768" class="Bound">x</a>{% endraw %}</pre>
However, there are no possible values of type `A → ⊥`
when `A` is anything other than `⊥` itself.


### Exercise (`≢`, `<-irrerflexive`)

Using negation, show that [strict inequality]({{ site.baseurl }}{% link out/plfa/Relations.md %}/#strict-inequality)
is irreflexive, that is, `n < n` holds for no `n`.


### Exercise (`trichotomy`)

Show that strict inequality satisfies [trichotomy]({{ site.baseurl }}{% link out/plfa/Relations.md %}/#trichotomy),
that is, for any naturals `m` and `n` exactly one of the following holds:

* `m < n`
* `m ≡ n`
* `m > n`

Here "exactly one" means that one must hold, and each implies the
negation of the other two.


### Exercise (`⊎-dual-×`)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.
<pre class="Agda">{% raw %}<a id="⊎-Dual-×"></a><a id="5573" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5573" class="Function">⊎-Dual-×</a> <a id="5582" class="Symbol">:</a> <a id="5584" class="PrimitiveType">Set₁</a>
<a id="5589" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5573" class="Function">⊎-Dual-×</a> <a id="5598" class="Symbol">=</a> <a id="5600" class="Symbol">∀</a> <a id="5602" class="Symbol">{</a><a id="5603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5603" class="Bound">A</a> <a id="5605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5605" class="Bound">B</a> <a id="5607" class="Symbol">:</a> <a id="5609" class="PrimitiveType">Set</a><a id="5612" class="Symbol">}</a> <a id="5614" class="Symbol">→</a> <a id="5616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="5618" class="Symbol">(</a><a id="5619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5603" class="Bound">A</a> <a id="5621" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#414" class="Datatype Operator">⊎</a> <a id="5623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5605" class="Bound">B</a><a id="5624" class="Symbol">)</a> <a id="5626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4104" class="Record Operator">≃</a> <a id="5628" class="Symbol">(</a><a id="5629" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="5631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5603" class="Bound">A</a><a id="5632" class="Symbol">)</a> <a id="5634" href="https://agda.github.io/agda-stdlib/Data.Product.html#1329" class="Function Operator">×</a> <a id="5636" class="Symbol">(</a><a id="5637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="5639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5605" class="Bound">B</a><a id="5640" class="Symbol">)</a>{% endraw %}</pre>
Show there is a term of type `⊎-Dual-×`.
This result is an easy consequence of something we've proved previously.

Is there also a term of the following type?
<pre class="Agda">{% raw %}<a id="×-Dual-⊎"></a><a id="5825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5825" class="Function">×-Dual-⊎</a> <a id="5834" class="Symbol">:</a> <a id="5836" class="PrimitiveType">Set₁</a>
<a id="5841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5825" class="Function">×-Dual-⊎</a> <a id="5850" class="Symbol">=</a> <a id="5852" class="Symbol">∀</a> <a id="5854" class="Symbol">{</a><a id="5855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5855" class="Bound">A</a> <a id="5857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5857" class="Bound">B</a> <a id="5859" class="Symbol">:</a> <a id="5861" class="PrimitiveType">Set</a><a id="5864" class="Symbol">}</a> <a id="5866" class="Symbol">→</a> <a id="5868" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="5870" class="Symbol">(</a><a id="5871" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5855" class="Bound">A</a> <a id="5873" href="https://agda.github.io/agda-stdlib/Data.Product.html#1329" class="Function Operator">×</a> <a id="5875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5857" class="Bound">B</a><a id="5876" class="Symbol">)</a> <a id="5878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Isomorphism.md %}{% raw %}#4104" class="Record Operator">≃</a> <a id="5880" class="Symbol">(</a><a id="5881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="5883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5855" class="Bound">A</a><a id="5884" class="Symbol">)</a> <a id="5886" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#414" class="Datatype Operator">⊎</a> <a id="5888" class="Symbol">(</a><a id="5889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="5891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#5857" class="Bound">B</a><a id="5892" class="Symbol">)</a>{% endraw %}</pre>
If so, prove; if not, explain why.


## Intuitive and Classical logic

In Gilbert and Sullivan's *The Gondoliers*, Casilda is told that
as an infant she was married to the heir of the King of Batavia, but
that due to a mix-up no one knows which of two individuals, Marco or
Giuseppe, is the heir.  Alarmed, she wails "Then do you mean to say
that I am married to one of two gondoliers, but it is impossible to
say which?"  To which the response is "Without any doubt of any kind
whatever."

Logic comes in many varieties, and one distinction is between
*classical* and *intuitionistic*. Intuitionists, concerned
by cavalier assumptions made by some logicians about the nature of
infinity, insist upon a constructionist notion of truth.  In
particular, they insist that a proof of `A ⊎ B` must show
*which* of `A` or `B` holds, and hence they would reject the
claim that Casilda is married to Marco or Giuseppe until one of the
two was identified as her husband.  Perhaps Gilbert and Sullivan
anticipated intuitionism, for their story's outcome is that the heir
turns out to be a third individual, Luiz, with whom Casilda is,
conveniently, already in love.

Intuitionists also reject the law of the excluded
middle, which asserts `A ⊎ ¬ A` for every `A`, since the law
gives no clue as to *which* of `A` or `¬ A` holds. Heyting
formalised a variant of Hilbert's classical logic that captures the
intuitionistic notion of provability. In particular, the law of the
excluded middle is provable in Hilbert's logic, but not in Heyting's.
Further, if the law of the excluded middle is added as an axiom to
Heyting's logic, then it becomes equivalent to Hilbert's.
Kolmogorov
showed the two logics were closely related: he gave a double-negation
translation, such that a formula is provable in classical logic if and
only if its translation is provable in intuitionistic logic.

Propositions as Types was first formulated for intuitionistic logic.
It is a perfect fit, because in the intuitionist interpretation the
formula `A ⊎ B` is provable exactly when one exhibits either a proof
of `A` or a proof of `B`, so the type corresponding to disjunction is
a disjoint sum.

(Parts of the above are adopted from "Propositions as Types", Philip Wadler,
*Communications of the ACM*, December 2015.)

## Excluded middle is irrefutable

The law of the excluded middle can be formulated as follows.
<pre class="Agda">{% raw %}<a id="EM"></a><a id="8302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8302" class="Function">EM</a> <a id="8305" class="Symbol">:</a> <a id="8307" class="PrimitiveType">Set₁</a>
<a id="8312" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8302" class="Function">EM</a> <a id="8315" class="Symbol">=</a> <a id="8317" class="Symbol">∀</a> <a id="8319" class="Symbol">{</a><a id="8320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8320" class="Bound">A</a> <a id="8322" class="Symbol">:</a> <a id="8324" class="PrimitiveType">Set</a><a id="8327" class="Symbol">}</a> <a id="8329" class="Symbol">→</a> <a id="8331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8320" class="Bound">A</a> <a id="8333" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#414" class="Datatype Operator">⊎</a> <a id="8335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="8337" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8320" class="Bound">A</a>{% endraw %}</pre>
As we noted, the law of the excluded middle does not hold in
intuitionistic logic.  However, we can show that it is *irrefutable*,
meaning that the negation of its negation is provable (and hence that
its negation is never provable).
<pre class="Agda">{% raw %}<a id="em-irrefutable"></a><a id="8597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8597" class="Function">em-irrefutable</a> <a id="8612" class="Symbol">:</a> <a id="8614" class="Symbol">∀</a> <a id="8616" class="Symbol">{</a><a id="8617" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8617" class="Bound">A</a> <a id="8619" class="Symbol">:</a> <a id="8621" class="PrimitiveType">Set</a><a id="8624" class="Symbol">}</a> <a id="8626" class="Symbol">→</a> <a id="8628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="8630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="8632" class="Symbol">(</a><a id="8633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8617" class="Bound">A</a> <a id="8635" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#414" class="Datatype Operator">⊎</a> <a id="8637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="8639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8617" class="Bound">A</a><a id="8640" class="Symbol">)</a>
<a id="8642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8597" class="Function">em-irrefutable</a> <a id="8657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8657" class="Bound">k</a> <a id="8659" class="Symbol">=</a> <a id="8661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8657" class="Bound">k</a> <a id="8663" class="Symbol">(</a><a id="8664" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#495" class="InductiveConstructor">inj₂</a> <a id="8669" class="Symbol">λ{</a> <a id="8672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8672" class="Bound">x</a> <a id="8674" class="Symbol">→</a> <a id="8676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8657" class="Bound">k</a> <a id="8678" class="Symbol">(</a><a id="8679" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#470" class="InductiveConstructor">inj₁</a> <a id="8684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#8672" class="Bound">x</a><a id="8685" class="Symbol">)</a> <a id="8687" class="Symbol">})</a>{% endraw %}</pre>
The best way to explain this code is to develop it interactively.

    em-irrefutable k = ?

Given evidence `k` that `¬ (A ⊎ ¬ A)`, that is, a function that give a
value of type `A ⊎ ¬ A` returns a value of the empty type, we must fill
in `?` with a term that returns a value of the empty type.  The only way
we can get a value of the empty type is by applying `k` itself, so let's
expand the hole accordingly.

    em-irrefutable k = k ?

We need to fill the new hole with a value of type `A ⊎ ¬ A`. We don't have
a value of type `A` to hand, so let's pick the second disjunct.

    em-irrefutable k = k (inj₂ λ{ x → ? })

The second disjunct accepts evidence of `¬ A`, that is, a function
that given a value of type `A` returns a value of the empty type.  We
bind `x` to the value of type `A`, and now we need to fill in the hole
with a value of the empty type.  Once again, he only way we can get a
value of the empty type is by applying `k` itself, so let's expand the
hole accordingly.

    em-irrefutable k = k (inj₂ λ{ x → k ? })

This time we do have a value of type `A` to hand, namely `x`, so we can
pick the first disjunct.

    em-irrefutable k = k (inj₂ λ{ x → k (inj₁ x) })

There are no holes left! This completes the proof.

The following story illustrates the behaviour of the term we have created.
(With apologies to Peter Selinger, who tells a similar story
about a king, a wizard, and the Philosopher's stone.)

Once upon a time, the devil approached a man and made an offer:
"Either (a) I will give you one billion dollars, or (b) I will grant
you any wish if you pay me one billion dollars.
Of course, I get to choose whether I offer (a) or (b)."

The man was wary.  Did he need to sign over his soul?
No, said the devil, all the man need do is accept the offer.

The man pondered.  If he was offered (b) it was unlikely that he would
ever be able to buy the wish, but what was the harm in having the
opportunity available?

"I accept," said the man at last.  "Do I get (a) or (b)?"

The devil paused.  "I choose (b)."

The man was disappointed but not surprised.  That was that, he thought.
But the offer gnawed at him.  Imagine what he could do with his wish!
Many years passed, and the man began to accumulate money.  To get the
money he sometimes did bad things, and dimly he realised that
this must be what the devil had in mind.
Eventually he had his billion dollars, and the devil appeared again.

"Here is a billion dollars," said the man, handing over a valise
containing the money.  "Grant me my wish!"

The devil took possession of the valise.  Then he said, "Oh, did I say
(b) before?  I'm so sorry.  I meant (a).  It is my great pleasure to
give you one billion dollars."

And the devil handed back to the man the same valise that the man had
just handed to him.

(Parts of the above are adopted from "Call-by-Value is Dual to Call-by-Name",
Philip Wadler, *International Conference on Functional Programming*, 2003.)


### Exercise

Prove the following four formulas are equivalent to each other,
and to the formula `EM` given earlier.
<pre class="Agda">{% raw %}<a id="¬¬-Elim"></a><a id="11786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11786" class="Function">¬¬-Elim</a> <a id="Peirce"></a><a id="11794" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11794" class="Function">Peirce</a> <a id="Implication"></a><a id="11801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11801" class="Function">Implication</a> <a id="11813" class="Symbol">:</a> <a id="11815" class="PrimitiveType">Set₁</a>
<a id="11820" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11786" class="Function">¬¬-Elim</a> <a id="11828" class="Symbol">=</a> <a id="11830" class="Symbol">∀</a> <a id="11832" class="Symbol">{</a><a id="11833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11833" class="Bound">A</a> <a id="11835" class="Symbol">:</a> <a id="11837" class="PrimitiveType">Set</a><a id="11840" class="Symbol">}</a> <a id="11842" class="Symbol">→</a> <a id="11844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="11846" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="11848" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11833" class="Bound">A</a> <a id="11850" class="Symbol">→</a> <a id="11852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11833" class="Bound">A</a>
<a id="11854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11794" class="Function">Peirce</a> <a id="11861" class="Symbol">=</a> <a id="11863" class="Symbol">∀</a> <a id="11865" class="Symbol">{</a><a id="11866" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11866" class="Bound">A</a> <a id="11868" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11868" class="Bound">B</a> <a id="11870" class="Symbol">:</a> <a id="11872" class="PrimitiveType">Set</a><a id="11875" class="Symbol">}</a> <a id="11877" class="Symbol">→</a> <a id="11879" class="Symbol">(((</a><a id="11882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11866" class="Bound">A</a> <a id="11884" class="Symbol">→</a> <a id="11886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11868" class="Bound">B</a><a id="11887" class="Symbol">)</a> <a id="11889" class="Symbol">→</a> <a id="11891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11866" class="Bound">A</a><a id="11892" class="Symbol">)</a> <a id="11894" class="Symbol">→</a> <a id="11896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11866" class="Bound">A</a><a id="11897" class="Symbol">)</a>
<a id="11899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11801" class="Function">Implication</a> <a id="11911" class="Symbol">=</a> <a id="11913" class="Symbol">∀</a> <a id="11915" class="Symbol">{</a><a id="11916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11916" class="Bound">A</a> <a id="11918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11918" class="Bound">B</a> <a id="11920" class="Symbol">:</a> <a id="11922" class="PrimitiveType">Set</a><a id="11925" class="Symbol">}</a> <a id="11927" class="Symbol">→</a> <a id="11929" class="Symbol">(</a><a id="11930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11916" class="Bound">A</a> <a id="11932" class="Symbol">→</a> <a id="11934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11918" class="Bound">B</a><a id="11935" class="Symbol">)</a> <a id="11937" class="Symbol">→</a> <a id="11939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="11941" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11916" class="Bound">A</a> <a id="11943" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#414" class="Datatype Operator">⊎</a> <a id="11945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11918" class="Bound">B</a>
<a id="×-Implies-⊎"></a><a id="11947" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11947" class="Function">×-Implies-⊎</a> <a id="11959" class="Symbol">=</a> <a id="11961" class="Symbol">∀</a> <a id="11963" class="Symbol">{</a><a id="11964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11964" class="Bound">A</a> <a id="11966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11966" class="Bound">B</a> <a id="11968" class="Symbol">:</a> <a id="11970" class="PrimitiveType">Set</a><a id="11973" class="Symbol">}</a> <a id="11975" class="Symbol">→</a> <a id="11977" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="11979" class="Symbol">(</a><a id="11980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11964" class="Bound">A</a> <a id="11982" href="https://agda.github.io/agda-stdlib/Data.Product.html#1329" class="Function Operator">×</a> <a id="11984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11966" class="Bound">B</a><a id="11985" class="Symbol">)</a> <a id="11987" class="Symbol">→</a> <a id="11989" class="Symbol">(</a><a id="11990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="11992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11964" class="Bound">A</a><a id="11993" class="Symbol">)</a> <a id="11995" href="https://agda.github.io/agda-stdlib/Data.Sum.Base.html#414" class="Datatype Operator">⊎</a> <a id="11997" class="Symbol">(</a><a id="11998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="12000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#11966" class="Bound">B</a><a id="12001" class="Symbol">)</a>{% endraw %}</pre>


### Exercise (`¬-stable`, `×-stable`)

Say that a formula is *stable* if double negation elimination holds for it.
<pre class="Agda">{% raw %}<a id="Stable"></a><a id="12144" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12144" class="Function">Stable</a> <a id="12151" class="Symbol">:</a> <a id="12153" class="PrimitiveType">Set</a> <a id="12157" class="Symbol">→</a> <a id="12159" class="PrimitiveType">Set</a>
<a id="12163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12144" class="Function">Stable</a> <a id="12170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12170" class="Bound">A</a> <a id="12172" class="Symbol">=</a> <a id="12174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="12176" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="12178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12170" class="Bound">A</a> <a id="12180" class="Symbol">→</a> <a id="12182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12170" class="Bound">A</a>{% endraw %}</pre>
Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.
<pre class="Agda">{% raw %}<a id="12308" class="Keyword">postulate</a>
  <a id="¬-stable"></a><a id="12320" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12320" class="Postulate">¬-stable</a> <a id="12329" class="Symbol">:</a> <a id="12331" class="Symbol">∀</a> <a id="12333" class="Symbol">{</a><a id="12334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12334" class="Bound">A</a> <a id="12336" class="Symbol">:</a> <a id="12338" class="PrimitiveType">Set</a><a id="12341" class="Symbol">}</a> <a id="12343" class="Symbol">→</a> <a id="12345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12144" class="Function">Stable</a> <a id="12352" class="Symbol">(</a><a id="12353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#846" class="Function Operator">¬</a> <a id="12355" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12334" class="Bound">A</a><a id="12356" class="Symbol">)</a>
  <a id="×-stable"></a><a id="12360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12360" class="Postulate">×-stable</a> <a id="12369" class="Symbol">:</a> <a id="12371" class="Symbol">∀</a> <a id="12373" class="Symbol">{</a><a id="12374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12374" class="Bound">A</a> <a id="12376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12376" class="Bound">B</a> <a id="12378" class="Symbol">:</a> <a id="12380" class="PrimitiveType">Set</a><a id="12383" class="Symbol">}</a> <a id="12385" class="Symbol">→</a> <a id="12387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12144" class="Function">Stable</a> <a id="12394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12374" class="Bound">A</a> <a id="12396" class="Symbol">→</a> <a id="12398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12144" class="Function">Stable</a> <a id="12405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12376" class="Bound">B</a> <a id="12407" class="Symbol">→</a> <a id="12409" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12144" class="Function">Stable</a> <a id="12416" class="Symbol">(</a><a id="12417" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12374" class="Bound">A</a> <a id="12419" href="https://agda.github.io/agda-stdlib/Data.Product.html#1329" class="Function Operator">×</a> <a id="12421" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Negation.md %}{% raw %}#12376" class="Bound">B</a><a id="12422" class="Symbol">)</a>{% endraw %}</pre>

## Standard Prelude

Definitions similar to those in this chapter can be found in the standard library.
<pre class="Agda">{% raw %}<a id="12553" class="Keyword">import</a> <a id="12560" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="12577" class="Keyword">using</a> <a id="12583" class="Symbol">(</a><a id="12584" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#464" class="Function Operator">¬_</a><a id="12586" class="Symbol">)</a>
<a id="12588" class="Keyword">import</a> <a id="12595" href="https://agda.github.io/agda-stdlib/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="12621" class="Keyword">using</a> <a id="12627" class="Symbol">(</a><a id="12628" href="https://agda.github.io/agda-stdlib/Relation.Nullary.Negation.html#688" class="Function">contraposition</a><a id="12642" class="Symbol">)</a>{% endraw %}</pre>

## Unicode

This chapter uses the following unicode.

    ¬  U+00AC  NOT SIGN (\neg)

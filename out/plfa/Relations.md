---
title     : "Relations: Inductive definition of relations"
layout    : page
permalink : /Relations/
---

<pre class="Agda">{% raw %}<a id="123" class="Keyword">module</a> <a id="130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="145" class="Keyword">where</a>{% endraw %}</pre>

After having defined operations such as addition and multiplication,
the next step is to define relations, such as *less than or equal*.

## Imports

<pre class="Agda">{% raw %}<a id="326" class="Keyword">import</a> <a id="333" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="371" class="Symbol">as</a> <a id="374" class="Module">Eq</a>
<a id="377" class="Keyword">open</a> <a id="382" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="385" class="Keyword">using</a> <a id="391" class="Symbol">(</a><a id="392" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="395" class="Symbol">;</a> <a id="397" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="401" class="Symbol">;</a> <a id="403" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a><a id="407" class="Symbol">;</a> <a id="409" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#560" class="Function">sym</a><a id="412" class="Symbol">)</a>
<a id="414" class="Keyword">open</a> <a id="419" class="Keyword">import</a> <a id="426" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="435" class="Keyword">using</a> <a id="441" class="Symbol">(</a><a id="442" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="443" class="Symbol">;</a> <a id="445" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="449" class="Symbol">;</a> <a id="451" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="454" class="Symbol">;</a> <a id="456" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="459" class="Symbol">;</a> <a id="461" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="464" class="Symbol">;</a> <a id="466" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="469" class="Symbol">)</a>
<a id="471" class="Keyword">open</a> <a id="476" class="Keyword">import</a> <a id="483" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="503" class="Keyword">using</a> <a id="509" class="Symbol">(</a><a id="510" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8115" class="Function">+-comm</a><a id="516" class="Symbol">;</a> <a id="518" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7679" class="Function">+-suc</a><a id="523" class="Symbol">)</a>{% endraw %}</pre>


## Defining relations

The relation *less than or equal* has an infinite number of
instances.  Here are a few of them:

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
<pre class="Agda">{% raw %}<a id="1200" class="Keyword">data</a> <a id="_≤_"></a><a id="1205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">_≤_</a> <a id="1209" class="Symbol">:</a> <a id="1211" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1213" class="Symbol">→</a> <a id="1215" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1217" class="Symbol">→</a> <a id="1219" class="PrimitiveType">Set</a> <a id="1223" class="Keyword">where</a>
  <a id="_≤_.z≤n"></a><a id="1231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="1235" class="Symbol">:</a> <a id="1237" class="Symbol">∀</a> <a id="1239" class="Symbol">{</a><a id="1240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1240" class="Bound">n</a> <a id="1242" class="Symbol">:</a> <a id="1244" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1245" class="Symbol">}</a> <a id="1247" class="Symbol">→</a> <a id="1249" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="1254" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="1256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1240" class="Bound">n</a>
  <a id="_≤_.s≤s"></a><a id="1260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="1264" class="Symbol">:</a> <a id="1266" class="Symbol">∀</a> <a id="1268" class="Symbol">{</a><a id="1269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1269" class="Bound">m</a> <a id="1271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1271" class="Bound">n</a> <a id="1273" class="Symbol">:</a> <a id="1275" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1276" class="Symbol">}</a> <a id="1278" class="Symbol">→</a> <a id="1280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1269" class="Bound">m</a> <a id="1282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="1284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1271" class="Bound">n</a> <a id="1286" class="Symbol">→</a> <a id="1288" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1269" class="Bound">m</a> <a id="1294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="1296" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1271" class="Bound">n</a>{% endraw %}</pre>
Here `z≤n` and `s≤s` (with no spaces) are constructor names,
while `zero ≤ m`, and `m ≤ n` and `suc m ≤ suc n` (with spaces)
are types.  This is our first use of an *indexed* datatype,
where we say the type `m ≤ n` is indexed by two naturals, `m` and `n`.

Both definitions above tell us the same two things:

+ *Base case*: for all naturals `n`, the proposition `zero ≤ n` holds
+ *Inductive case*: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

+ *Base case*: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
+ *Inductive case*: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

For example, here in inference rule notation is the proof that
`2 ≤ 4`.

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof.
<pre class="Agda">{% raw %}<a id="2354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#2354" class="Function">_</a> <a id="2356" class="Symbol">:</a> <a id="2358" class="Number">2</a> <a id="2360" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="2362" class="Number">4</a>
<a id="2364" class="Symbol">_</a> <a id="2366" class="Symbol">=</a> <a id="2368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="2372" class="Symbol">(</a><a id="2373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="2377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a><a id="2380" class="Symbol">)</a>{% endraw %}</pre>


## Implicit arguments

This is our first use of implicit arguments.
In the definition of inequality, the two lines defining the constructors
use `∀`, very similar to our use of `∀` in propositions such as:

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }` rather than
parentheses `( )`.  This means that the arguments are *implicit* and need not be
written explicitly; instead, they are *inferred* by Agda's typechecker. Thus, we
write `+-comm m n` for the proof that `m + n ≡ n + m`, but `z≤n` for the proof
that `zero ≤ m`, leaving `m` implicit.  Similarly, if `m≤n` is evidence that
`m ≤ n`, we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving
both `m` and `n` implicit.

If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit.
<pre class="Agda">{% raw %}<a id="3372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3372" class="Function">_</a> <a id="3374" class="Symbol">:</a> <a id="3376" class="Number">2</a> <a id="3378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="3380" class="Number">4</a>
<a id="3382" class="Symbol">_</a> <a id="3384" class="Symbol">=</a> <a id="3386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="3390" class="Symbol">{</a><a id="3391" class="Number">1</a><a id="3392" class="Symbol">}</a> <a id="3394" class="Symbol">{</a><a id="3395" class="Number">3</a><a id="3396" class="Symbol">}</a> <a id="3398" class="Symbol">(</a><a id="3399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="3403" class="Symbol">{</a><a id="3404" class="Number">0</a><a id="3405" class="Symbol">}</a> <a id="3407" class="Symbol">{</a><a id="3408" class="Number">2</a><a id="3409" class="Symbol">}</a> <a id="3411" class="Symbol">(</a><a id="3412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="3416" class="Symbol">{</a><a id="3417" class="Number">2</a><a id="3418" class="Symbol">}))</a>{% endraw %}</pre>


## Precedence

We declare the precedence for comparison as follows.
<pre class="Agda">{% raw %}<a id="3516" class="Keyword">infix</a> <a id="3522" class="Number">4</a> <a id="3524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">_≤_</a>{% endraw %}</pre>
We set the precedence of `_≤_` at level 4, so it binds less tightly
that `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the first is
less than or equal to the second.  We don't give the code for doing so here, but
will return to this point in Chapter [Decidable]({{ site.baseurl }}{% link out/plfa/Decidable.md %}).


## Properties of ordering relations

Relations occur all the time, and mathematicians have agreed
on names for some of the most common properties.

+ *Reflexive* For all `n`, the relation `n ≤ n` holds.
+ *Transitive* For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
+ *Anti-symmetric* For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
+ *Total* For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

+ *Preorder* Any relation that is reflexive and transitive.
+ *Partial order* Any preorder that is also anti-symmetric.
+ *Total order* Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading
a technical paper, this gives you an easy way to orient yourself,
by checking whether or not it is a preorder, partial order, or total order.
A careful author will often make it explicit, for instance by saying
that a given relation is a preorder but not a partial order, or a
partial order but not a total order. (Can you think of examples of
such relations?)


## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.
<pre class="Agda">{% raw %}<a id="≤-refl"></a><a id="5710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5710" class="Function">≤-refl</a> <a id="5717" class="Symbol">:</a> <a id="5719" class="Symbol">∀</a> <a id="5721" class="Symbol">{</a><a id="5722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5722" class="Bound">n</a> <a id="5724" class="Symbol">:</a> <a id="5726" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="5727" class="Symbol">}</a> <a id="5729" class="Symbol">→</a> <a id="5731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5722" class="Bound">n</a> <a id="5733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="5735" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5722" class="Bound">n</a>
<a id="5737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5710" class="Function">≤-refl</a> <a id="5744" class="Symbol">{</a><a id="5745" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="5749" class="Symbol">}</a> <a id="5751" class="Symbol">=</a> <a id="5753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="5757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5710" class="Function">≤-refl</a> <a id="5764" class="Symbol">{</a><a id="5765" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5769" class="Bound">n</a><a id="5770" class="Symbol">}</a> <a id="5772" class="Symbol">=</a> <a id="5774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="5778" class="Symbol">(</a><a id="5779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5710" class="Function">≤-refl</a> <a id="5786" class="Symbol">{</a><a id="5787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5769" class="Bound">n</a><a id="5788" class="Symbol">})</a>{% endraw %}</pre>
The proof is a straightforward induction on `n`.  In the base case,
`zero ≤ zero` holds by `z≤n`.  In the inductive case, the inductive
hypothesis `≤-refl n` gives us a proof of `n ≤ n`, and applying `s≤s`
to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤
p` hold, then `m ≤ p` holds.
<pre class="Agda">{% raw %}<a id="≤-trans"></a><a id="6374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6374" class="Function">≤-trans</a> <a id="6382" class="Symbol">:</a> <a id="6384" class="Symbol">∀</a> <a id="6386" class="Symbol">{</a><a id="6387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6387" class="Bound">m</a> <a id="6389" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6389" class="Bound">n</a> <a id="6391" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6391" class="Bound">p</a> <a id="6393" class="Symbol">:</a> <a id="6395" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="6396" class="Symbol">}</a> <a id="6398" class="Symbol">→</a> <a id="6400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6387" class="Bound">m</a> <a id="6402" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="6404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6389" class="Bound">n</a> <a id="6406" class="Symbol">→</a> <a id="6408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6389" class="Bound">n</a> <a id="6410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="6412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6391" class="Bound">p</a> <a id="6414" class="Symbol">→</a> <a id="6416" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6387" class="Bound">m</a> <a id="6418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="6420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6391" class="Bound">p</a>
<a id="6422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6374" class="Function">≤-trans</a> <a id="6430" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="6434" class="Symbol">_</a> <a id="6436" class="Symbol">=</a> <a id="6438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="6442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6374" class="Function">≤-trans</a> <a id="6450" class="Symbol">(</a><a id="6451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="6455" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6455" class="Bound">m≤n</a><a id="6458" class="Symbol">)</a> <a id="6460" class="Symbol">(</a><a id="6461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="6465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6465" class="Bound">n≤p</a><a id="6468" class="Symbol">)</a> <a id="6470" class="Symbol">=</a> <a id="6472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="6476" class="Symbol">(</a><a id="6477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6374" class="Function">≤-trans</a> <a id="6485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6455" class="Bound">m≤n</a> <a id="6489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6465" class="Bound">n≤p</a><a id="6492" class="Symbol">)</a>{% endraw %}</pre>
Here the proof is most easily thought of as by induction on the
*evidence* that `m ≤ n`, so we have left `m`, `n`, and `p` implicit.

In the base case, the first inequality holds by `z≤n`, and so
we are given `zero ≤ n` and `n ≤ p` and must show `zero ≤ p`,
which follows immediately by `z≤n`.  In this
case, the fact that `n ≤ p` is irrelevant, and we write `_` as the
pattern to indicate that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that
such a case cannot arise, and does not require it to be listed.

Alternatively, we could make the implicit parameters explicit.
<pre class="Agda">{% raw %}<a id="≤-trans′"></a><a id="7571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7571" class="Function">≤-trans′</a> <a id="7580" class="Symbol">:</a> <a id="7582" class="Symbol">∀</a> <a id="7584" class="Symbol">(</a><a id="7585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7585" class="Bound">m</a> <a id="7587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7587" class="Bound">n</a> <a id="7589" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7589" class="Bound">p</a> <a id="7591" class="Symbol">:</a> <a id="7593" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="7594" class="Symbol">)</a> <a id="7596" class="Symbol">→</a> <a id="7598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7585" class="Bound">m</a> <a id="7600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="7602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7587" class="Bound">n</a> <a id="7604" class="Symbol">→</a> <a id="7606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7587" class="Bound">n</a> <a id="7608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="7610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7589" class="Bound">p</a> <a id="7612" class="Symbol">→</a> <a id="7614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7585" class="Bound">m</a> <a id="7616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="7618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7589" class="Bound">p</a>
<a id="7620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7571" class="Function">≤-trans′</a> <a id="7629" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="7634" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7634" class="Bound">n</a> <a id="7636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7636" class="Bound">p</a> <a id="7638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="7642" class="Symbol">_</a> <a id="7644" class="Symbol">=</a> <a id="7646" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="7650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7571" class="Function">≤-trans′</a> <a id="7659" class="Symbol">(</a><a id="7660" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7664" class="Bound">m</a><a id="7665" class="Symbol">)</a> <a id="7667" class="Symbol">(</a><a id="7668" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7672" class="Bound">n</a><a id="7673" class="Symbol">)</a> <a id="7675" class="Symbol">(</a><a id="7676" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7680" class="Bound">p</a><a id="7681" class="Symbol">)</a> <a id="7683" class="Symbol">(</a><a id="7684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="7688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7688" class="Bound">m≤n</a><a id="7691" class="Symbol">)</a> <a id="7693" class="Symbol">(</a><a id="7694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="7698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7698" class="Bound">n≤p</a><a id="7701" class="Symbol">)</a> <a id="7703" class="Symbol">=</a> <a id="7705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="7709" class="Symbol">(</a><a id="7710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7571" class="Function">≤-trans′</a> <a id="7719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7664" class="Bound">m</a> <a id="7721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7672" class="Bound">n</a> <a id="7723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7680" class="Bound">p</a> <a id="7725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7688" class="Bound">m≤n</a> <a id="7729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7698" class="Bound">n≤p</a><a id="7732" class="Symbol">)</a>{% endraw %}</pre>
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

The technique of inducting on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on the
value of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Anti-symmetry

The third property to prove about comparison is that it is antisymmetric:
for all naturals `m` and `n`, if both `m ≤ n` and `n ≤ m` hold, then
`m ≡ n` holds.
<pre class="Agda">{% raw %}<a id="≤-antisym"></a><a id="8496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8496" class="Function">≤-antisym</a> <a id="8506" class="Symbol">:</a> <a id="8508" class="Symbol">∀</a> <a id="8510" class="Symbol">{</a><a id="8511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8511" class="Bound">m</a> <a id="8513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8513" class="Bound">n</a> <a id="8515" class="Symbol">:</a> <a id="8517" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="8518" class="Symbol">}</a> <a id="8520" class="Symbol">→</a> <a id="8522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8511" class="Bound">m</a> <a id="8524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="8526" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8513" class="Bound">n</a> <a id="8528" class="Symbol">→</a> <a id="8530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8513" class="Bound">n</a> <a id="8532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="8534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8511" class="Bound">m</a> <a id="8536" class="Symbol">→</a> <a id="8538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8511" class="Bound">m</a> <a id="8540" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="8542" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8513" class="Bound">n</a>
<a id="8544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8496" class="Function">≤-antisym</a> <a id="8554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="8558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a> <a id="8562" class="Symbol">=</a> <a id="8564" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="8569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8496" class="Function">≤-antisym</a> <a id="8579" class="Symbol">(</a><a id="8580" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="8584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8584" class="Bound">m≤n</a><a id="8587" class="Symbol">)</a> <a id="8589" class="Symbol">(</a><a id="8590" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="8594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8594" class="Bound">n≤m</a><a id="8597" class="Symbol">)</a> <a id="8599" class="Symbol">=</a> <a id="8601" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#1075" class="Function">cong</a> <a id="8606" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8610" class="Symbol">(</a><a id="8611" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8496" class="Function">≤-antisym</a> <a id="8621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8584" class="Bound">m≤n</a> <a id="8625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8594" class="Bound">n≤m</a><a id="8628" class="Symbol">)</a>{% endraw %}</pre>
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold, and so we have left `m` and `n` implicit.

In the base case, both inequalities hold by `z≤n`,
and so we are given `zero ≤ zero` and `zero ≤ zero` and must
show `zero ≡ zero`, which follows by reflexivity.  (Reflexivity
of equality, that is, not reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality holds by `s≤s n≤m`, and so we are
given `suc m ≤ suc n` and `suc n ≤ suc m` and must show `suc m ≡ suc n`.
The inductive hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`,
and our goal follows by congruence.

### Exercise (≤-antisym-cases)

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?


## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total.
<pre class="Agda">{% raw %}<a id="9680" class="Keyword">data</a> <a id="Total"></a><a id="9685" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9685" class="Datatype">Total</a> <a id="9691" class="Symbol">(</a><a id="9692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9692" class="Bound">m</a> <a id="9694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9694" class="Bound">n</a> <a id="9696" class="Symbol">:</a> <a id="9698" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="9699" class="Symbol">)</a> <a id="9701" class="Symbol">:</a> <a id="9703" class="PrimitiveType">Set</a> <a id="9707" class="Keyword">where</a>
  <a id="Total.forward"></a><a id="9715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9715" class="InductiveConstructor">forward</a> <a id="9723" class="Symbol">:</a> <a id="9725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9692" class="Bound">m</a> <a id="9727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="9729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9694" class="Bound">n</a> <a id="9731" class="Symbol">→</a> <a id="9733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9685" class="Datatype">Total</a> <a id="9739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9692" class="Bound">m</a> <a id="9741" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9694" class="Bound">n</a>
  <a id="Total.flipped"></a><a id="9745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9745" class="InductiveConstructor">flipped</a> <a id="9753" class="Symbol">:</a> <a id="9755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9694" class="Bound">n</a> <a id="9757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="9759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9692" class="Bound">m</a> <a id="9761" class="Symbol">→</a> <a id="9763" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9685" class="Datatype">Total</a> <a id="9769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9692" class="Bound">m</a> <a id="9771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9694" class="Bound">n</a>{% endraw %}</pre>
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

This is our first use of a datatype with *parameters*,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype.
<pre class="Agda">{% raw %}<a id="10090" class="Keyword">data</a> <a id="Total′"></a><a id="10095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10095" class="Datatype">Total′</a> <a id="10102" class="Symbol">:</a> <a id="10104" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="10106" class="Symbol">→</a> <a id="10108" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="10110" class="Symbol">→</a> <a id="10112" class="PrimitiveType">Set</a> <a id="10116" class="Keyword">where</a>
  <a id="Total′.forward′"></a><a id="10124" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10124" class="InductiveConstructor">forward′</a> <a id="10133" class="Symbol">:</a> <a id="10135" class="Symbol">∀</a> <a id="10137" class="Symbol">{</a><a id="10138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10138" class="Bound">m</a> <a id="10140" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10140" class="Bound">n</a> <a id="10142" class="Symbol">:</a> <a id="10144" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10145" class="Symbol">}</a> <a id="10147" class="Symbol">→</a> <a id="10149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10138" class="Bound">m</a> <a id="10151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="10153" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10140" class="Bound">n</a> <a id="10155" class="Symbol">→</a> <a id="10157" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10095" class="Datatype">Total′</a> <a id="10164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10138" class="Bound">m</a> <a id="10166" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10140" class="Bound">n</a>
  <a id="Total′.flipped′"></a><a id="10170" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10170" class="InductiveConstructor">flipped′</a> <a id="10179" class="Symbol">:</a> <a id="10181" class="Symbol">∀</a> <a id="10183" class="Symbol">{</a><a id="10184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10184" class="Bound">m</a> <a id="10186" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10186" class="Bound">n</a> <a id="10188" class="Symbol">:</a> <a id="10190" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10191" class="Symbol">}</a> <a id="10193" class="Symbol">→</a> <a id="10195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10186" class="Bound">n</a> <a id="10197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="10199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10184" class="Bound">m</a> <a id="10201" class="Symbol">→</a> <a id="10203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10095" class="Datatype">Total′</a> <a id="10210" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10184" class="Bound">m</a> <a id="10212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10186" class="Bound">n</a>{% endraw %}</pre>
Each parameter of the type translates as an implicit
parameter of each constructor.
Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised
datatype the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and let Agda
exploit the uniformity of the parameters, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality.
<pre class="Agda">{% raw %}<a id="≤-total"></a><a id="10752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10752" class="Function">≤-total</a> <a id="10760" class="Symbol">:</a> <a id="10762" class="Symbol">∀</a> <a id="10764" class="Symbol">(</a><a id="10765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10765" class="Bound">m</a> <a id="10767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10767" class="Bound">n</a> <a id="10769" class="Symbol">:</a> <a id="10771" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10772" class="Symbol">)</a> <a id="10774" class="Symbol">→</a> <a id="10776" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9685" class="Datatype">Total</a> <a id="10782" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10765" class="Bound">m</a> <a id="10784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10767" class="Bound">n</a>
<a id="10786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10752" class="Function">≤-total</a> <a id="10794" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="10802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10802" class="Bound">n</a>                         <a id="10828" class="Symbol">=</a>  <a id="10831" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9715" class="InductiveConstructor">forward</a> <a id="10839" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="10843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10752" class="Function">≤-total</a> <a id="10851" class="Symbol">(</a><a id="10852" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10856" class="Bound">m</a><a id="10857" class="Symbol">)</a> <a id="10859" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="10885" class="Symbol">=</a>  <a id="10888" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9745" class="InductiveConstructor">flipped</a> <a id="10896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="10900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10752" class="Function">≤-total</a> <a id="10908" class="Symbol">(</a><a id="10909" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10913" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10913" class="Bound">m</a><a id="10914" class="Symbol">)</a> <a id="10916" class="Symbol">(</a><a id="10917" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10921" class="Bound">n</a><a id="10922" class="Symbol">)</a> <a id="10924" class="Keyword">with</a> <a id="10929" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10752" class="Function">≤-total</a> <a id="10937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10913" class="Bound">m</a> <a id="10939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10921" class="Bound">n</a>
<a id="10941" class="Symbol">...</a>                        <a id="10968" class="Symbol">|</a> <a id="10970" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9715" class="InductiveConstructor">forward</a> <a id="10978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10978" class="Bound">m≤n</a>  <a id="10983" class="Symbol">=</a>  <a id="10986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9715" class="InductiveConstructor">forward</a> <a id="10994" class="Symbol">(</a><a id="10995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="10999" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10978" class="Bound">m≤n</a><a id="11002" class="Symbol">)</a>
<a id="11004" class="Symbol">...</a>                        <a id="11031" class="Symbol">|</a> <a id="11033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9745" class="InductiveConstructor">flipped</a> <a id="11041" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11041" class="Bound">n≤m</a>  <a id="11046" class="Symbol">=</a>  <a id="11049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9745" class="InductiveConstructor">flipped</a> <a id="11057" class="Symbol">(</a><a id="11058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="11062" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11041" class="Bound">n≤m</a><a id="11065" class="Symbol">)</a>{% endraw %}</pre>
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

+ *First base case*: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

+ *Second base case*: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

+ *Inductive case*: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  - The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  - The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following.
<pre class="Agda">{% raw %}<a id="≤-total′"></a><a id="12573" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12573" class="Function">≤-total′</a> <a id="12582" class="Symbol">:</a> <a id="12584" class="Symbol">∀</a> <a id="12586" class="Symbol">(</a><a id="12587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12587" class="Bound">m</a> <a id="12589" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12589" class="Bound">n</a> <a id="12591" class="Symbol">:</a> <a id="12593" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="12594" class="Symbol">)</a> <a id="12596" class="Symbol">→</a> <a id="12598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9685" class="Datatype">Total</a> <a id="12604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12587" class="Bound">m</a> <a id="12606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12589" class="Bound">n</a>
<a id="12608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12573" class="Function">≤-total′</a> <a id="12617" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="12625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12625" class="Bound">n</a>        <a id="12634" class="Symbol">=</a>  <a id="12637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9715" class="InductiveConstructor">forward</a> <a id="12645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="12649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12573" class="Function">≤-total′</a> <a id="12658" class="Symbol">(</a><a id="12659" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12663" class="Bound">m</a><a id="12664" class="Symbol">)</a> <a id="12666" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>     <a id="12675" class="Symbol">=</a>  <a id="12678" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9745" class="InductiveConstructor">flipped</a> <a id="12686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="12690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12573" class="Function">≤-total′</a> <a id="12699" class="Symbol">(</a><a id="12700" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12704" class="Bound">m</a><a id="12705" class="Symbol">)</a> <a id="12707" class="Symbol">(</a><a id="12708" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12712" class="Bound">n</a><a id="12713" class="Symbol">)</a>  <a id="12716" class="Symbol">=</a>  <a id="12719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12751" class="Function">helper</a> <a id="12726" class="Symbol">(</a><a id="12727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12573" class="Function">≤-total′</a> <a id="12736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12704" class="Bound">m</a> <a id="12738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12712" class="Bound">n</a><a id="12739" class="Symbol">)</a>
  <a id="12743" class="Keyword">where</a>
  <a id="12751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12751" class="Function">helper</a> <a id="12758" class="Symbol">:</a> <a id="12760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9685" class="Datatype">Total</a> <a id="12766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12704" class="Bound">m</a> <a id="12768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12712" class="Bound">n</a> <a id="12770" class="Symbol">→</a> <a id="12772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9685" class="Datatype">Total</a> <a id="12778" class="Symbol">(</a><a id="12779" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12704" class="Bound">m</a><a id="12784" class="Symbol">)</a> <a id="12786" class="Symbol">(</a><a id="12787" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12712" class="Bound">n</a><a id="12792" class="Symbol">)</a>
  <a id="12796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12751" class="Function">helper</a> <a id="12803" class="Symbol">(</a><a id="12804" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9715" class="InductiveConstructor">forward</a> <a id="12812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12812" class="Bound">m≤n</a><a id="12815" class="Symbol">)</a>  <a id="12818" class="Symbol">=</a>  <a id="12821" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9715" class="InductiveConstructor">forward</a> <a id="12829" class="Symbol">(</a><a id="12830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="12834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12812" class="Bound">m≤n</a><a id="12837" class="Symbol">)</a>
  <a id="12841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12751" class="Function">helper</a> <a id="12848" class="Symbol">(</a><a id="12849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9745" class="InductiveConstructor">flipped</a> <a id="12857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12857" class="Bound">n≤m</a><a id="12860" class="Symbol">)</a>  <a id="12863" class="Symbol">=</a>  <a id="12866" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9745" class="InductiveConstructor">flipped</a> <a id="12874" class="Symbol">(</a><a id="12875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="12879" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12857" class="Bound">n≤m</a><a id="12882" class="Symbol">)</a>{% endraw %}</pre>
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound of the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case.
<pre class="Agda">{% raw %}<a id="≤-total″"></a><a id="13520" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13520" class="Function">≤-total″</a> <a id="13529" class="Symbol">:</a> <a id="13531" class="Symbol">∀</a> <a id="13533" class="Symbol">(</a><a id="13534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13534" class="Bound">m</a> <a id="13536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13536" class="Bound">n</a> <a id="13538" class="Symbol">:</a> <a id="13540" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="13541" class="Symbol">)</a> <a id="13543" class="Symbol">→</a> <a id="13545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9685" class="Datatype">Total</a> <a id="13551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13534" class="Bound">m</a> <a id="13553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13536" class="Bound">n</a>
<a id="13555" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13520" class="Function">≤-total″</a> <a id="13564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13564" class="Bound">m</a>       <a id="13572" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="13598" class="Symbol">=</a>  <a id="13601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9745" class="InductiveConstructor">flipped</a> <a id="13609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="13613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13520" class="Function">≤-total″</a> <a id="13622" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="13630" class="Symbol">(</a><a id="13631" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13635" class="Bound">n</a><a id="13636" class="Symbol">)</a>                   <a id="13656" class="Symbol">=</a>  <a id="13659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9715" class="InductiveConstructor">forward</a> <a id="13667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1231" class="InductiveConstructor">z≤n</a>
<a id="13671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13520" class="Function">≤-total″</a> <a id="13680" class="Symbol">(</a><a id="13681" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13685" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13685" class="Bound">m</a><a id="13686" class="Symbol">)</a> <a id="13688" class="Symbol">(</a><a id="13689" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13693" class="Bound">n</a><a id="13694" class="Symbol">)</a> <a id="13696" class="Keyword">with</a> <a id="13701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13520" class="Function">≤-total″</a> <a id="13710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13685" class="Bound">m</a> <a id="13712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13693" class="Bound">n</a>
<a id="13714" class="Symbol">...</a>                        <a id="13741" class="Symbol">|</a> <a id="13743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9715" class="InductiveConstructor">forward</a> <a id="13751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13751" class="Bound">m≤n</a>   <a id="13757" class="Symbol">=</a>  <a id="13760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9715" class="InductiveConstructor">forward</a> <a id="13768" class="Symbol">(</a><a id="13769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="13773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13751" class="Bound">m≤n</a><a id="13776" class="Symbol">)</a>
<a id="13778" class="Symbol">...</a>                        <a id="13805" class="Symbol">|</a> <a id="13807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9745" class="InductiveConstructor">flipped</a> <a id="13815" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13815" class="Bound">n≤m</a>   <a id="13821" class="Symbol">=</a>  <a id="13824" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9745" class="InductiveConstructor">flipped</a> <a id="13832" class="Symbol">(</a><a id="13833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="13837" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13815" class="Bound">n≤m</a><a id="13840" class="Symbol">)</a>{% endraw %}</pre>
It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is *monotonic* with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right.
<pre class="Agda">{% raw %}<a id="+-monoʳ-≤"></a><a id="14444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14444" class="Function">+-monoʳ-≤</a> <a id="14454" class="Symbol">:</a> <a id="14456" class="Symbol">∀</a> <a id="14458" class="Symbol">(</a><a id="14459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14459" class="Bound">m</a> <a id="14461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14461" class="Bound">p</a> <a id="14463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14463" class="Bound">q</a> <a id="14465" class="Symbol">:</a> <a id="14467" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14468" class="Symbol">)</a> <a id="14470" class="Symbol">→</a> <a id="14472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14461" class="Bound">p</a> <a id="14474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="14476" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14463" class="Bound">q</a> <a id="14478" class="Symbol">→</a> <a id="14480" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14459" class="Bound">m</a> <a id="14482" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14484" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14461" class="Bound">p</a> <a id="14486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="14488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14459" class="Bound">m</a> <a id="14490" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14463" class="Bound">q</a>
<a id="14494" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14444" class="Function">+-monoʳ-≤</a> <a id="14504" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="14512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14512" class="Bound">p</a> <a id="14514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14514" class="Bound">q</a> <a id="14516" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14516" class="Bound">p≤q</a>  <a id="14521" class="Symbol">=</a>  <a id="14524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14516" class="Bound">p≤q</a>
<a id="14528" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14444" class="Function">+-monoʳ-≤</a> <a id="14538" class="Symbol">(</a><a id="14539" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14543" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14543" class="Bound">m</a><a id="14544" class="Symbol">)</a> <a id="14546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14546" class="Bound">p</a> <a id="14548" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14548" class="Bound">q</a> <a id="14550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14550" class="Bound">p≤q</a>  <a id="14555" class="Symbol">=</a>  <a id="14558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1260" class="InductiveConstructor">s≤s</a> <a id="14562" class="Symbol">(</a><a id="14563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14444" class="Function">+-monoʳ-≤</a> <a id="14573" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14543" class="Bound">m</a> <a id="14575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14546" class="Bound">p</a> <a id="14577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14548" class="Bound">q</a> <a id="14579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14550" class="Bound">p≤q</a><a id="14582" class="Symbol">)</a>{% endraw %}</pre>
The proof is by induction on the first argument.

+ *Base case*: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

+ *Inductive case*: The first argument is `suc m`, in which case
  `suc m + p ≤ suc m + q` simplifies to `suc (m + p) ≤ suc (m + q)`.
  The inductive hypothesis `+-monoʳ-≤ m p q p≤q` establishes that
  `m + p ≤ m + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition.
<pre class="Agda">{% raw %}<a id="+-monoˡ-≤"></a><a id="15238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15238" class="Function">+-monoˡ-≤</a> <a id="15248" class="Symbol">:</a> <a id="15250" class="Symbol">∀</a> <a id="15252" class="Symbol">(</a><a id="15253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15253" class="Bound">m</a> <a id="15255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15255" class="Bound">n</a> <a id="15257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15257" class="Bound">p</a> <a id="15259" class="Symbol">:</a> <a id="15261" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="15262" class="Symbol">)</a> <a id="15264" class="Symbol">→</a> <a id="15266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15253" class="Bound">m</a> <a id="15268" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="15270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15255" class="Bound">n</a> <a id="15272" class="Symbol">→</a> <a id="15274" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15253" class="Bound">m</a> <a id="15276" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15278" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15257" class="Bound">p</a> <a id="15280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="15282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15255" class="Bound">n</a> <a id="15284" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15286" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15257" class="Bound">p</a>
<a id="15288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15238" class="Function">+-monoˡ-≤</a> <a id="15298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15298" class="Bound">m</a> <a id="15300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15300" class="Bound">n</a> <a id="15302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15302" class="Bound">p</a> <a id="15304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15304" class="Bound">m≤n</a> <a id="15308" class="Keyword">rewrite</a> <a id="15316" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8115" class="Function">+-comm</a> <a id="15323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15298" class="Bound">m</a> <a id="15325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15302" class="Bound">p</a> <a id="15327" class="Symbol">|</a> <a id="15329" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8115" class="Function">+-comm</a> <a id="15336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15300" class="Bound">n</a> <a id="15338" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15302" class="Bound">p</a> <a id="15340" class="Symbol">=</a> <a id="15342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14444" class="Function">+-monoʳ-≤</a> <a id="15352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15302" class="Bound">p</a> <a id="15354" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15298" class="Bound">m</a> <a id="15356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15300" class="Bound">n</a> <a id="15358" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15304" class="Bound">m≤n</a>{% endraw %}</pre>
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.
(Go ahead to read a chapter [Equality Rewriting expanded] for details how 
`rewrite` notation works internally).

Third, we combine the two previous results.
<pre class="Agda">{% raw %}<a id="+-mono-≤"></a><a id="15685" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15685" class="Function">+-mono-≤</a> <a id="15694" class="Symbol">:</a> <a id="15696" class="Symbol">∀</a> <a id="15698" class="Symbol">(</a><a id="15699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15699" class="Bound">m</a> <a id="15701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15701" class="Bound">n</a> <a id="15703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15703" class="Bound">p</a> <a id="15705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15705" class="Bound">q</a> <a id="15707" class="Symbol">:</a> <a id="15709" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="15710" class="Symbol">)</a> <a id="15712" class="Symbol">→</a> <a id="15714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15699" class="Bound">m</a> <a id="15716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="15718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15701" class="Bound">n</a> <a id="15720" class="Symbol">→</a> <a id="15722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15703" class="Bound">p</a> <a id="15724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="15726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15705" class="Bound">q</a> <a id="15728" class="Symbol">→</a> <a id="15730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15699" class="Bound">m</a> <a id="15732" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15703" class="Bound">p</a> <a id="15736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">≤</a> <a id="15738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15701" class="Bound">n</a> <a id="15740" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15705" class="Bound">q</a>
<a id="15744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15685" class="Function">+-mono-≤</a> <a id="15753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15753" class="Bound">m</a> <a id="15755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15755" class="Bound">n</a> <a id="15757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15757" class="Bound">p</a> <a id="15759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15759" class="Bound">q</a> <a id="15761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15761" class="Bound">m≤n</a> <a id="15765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15765" class="Bound">p≤q</a> <a id="15769" class="Symbol">=</a> <a id="15771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6374" class="Function">≤-trans</a> <a id="15779" class="Symbol">(</a><a id="15780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15238" class="Function">+-monoˡ-≤</a> <a id="15790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15753" class="Bound">m</a> <a id="15792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15755" class="Bound">n</a> <a id="15794" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15757" class="Bound">p</a> <a id="15796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15761" class="Bound">m≤n</a><a id="15799" class="Symbol">)</a> <a id="15801" class="Symbol">(</a><a id="15802" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14444" class="Function">+-monoʳ-≤</a> <a id="15812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15755" class="Bound">n</a> <a id="15814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15757" class="Bound">p</a> <a id="15816" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15759" class="Bound">q</a> <a id="15818" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15765" class="Bound">p≤q</a><a id="15821" class="Symbol">)</a>{% endraw %}</pre>
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.

### Exercise (stretch, `≤-reasoning`)

The proof of monotonicity (and the associated lemmas) can be written
in a more readable form by using an anologue of our notation for
`≡-reasoning`.  Read ahead to chapter [Equality]({{ site.baseurl }}{% link out/plfa/Equality.md %}) to
see how `≡-reasoning` is defined, define `≤-reasoning` analogously,
and use it to write out an alternative proof that addition is
monotonic with regard to inequality.


## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality.
<pre class="Agda">{% raw %}<a id="16588" class="Keyword">infix</a> <a id="16594" class="Number">4</a> <a id="16596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16606" class="Datatype Operator">_&lt;_</a>

<a id="16601" class="Keyword">data</a> <a id="_&lt;_"></a><a id="16606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16606" class="Datatype Operator">_&lt;_</a> <a id="16610" class="Symbol">:</a> <a id="16612" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="16614" class="Symbol">→</a> <a id="16616" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="16618" class="Symbol">→</a> <a id="16620" class="PrimitiveType">Set</a> <a id="16624" class="Keyword">where</a>
  <a id="_&lt;_.z&lt;s"></a><a id="16632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16632" class="InductiveConstructor">z&lt;s</a> <a id="16636" class="Symbol">:</a> <a id="16638" class="Symbol">∀</a> <a id="16640" class="Symbol">{</a><a id="16641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16641" class="Bound">n</a> <a id="16643" class="Symbol">:</a> <a id="16645" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16646" class="Symbol">}</a> <a id="16648" class="Symbol">→</a> <a id="16650" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="16655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16606" class="Datatype Operator">&lt;</a> <a id="16657" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16641" class="Bound">n</a>
  <a id="_&lt;_.s&lt;s"></a><a id="16665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16665" class="InductiveConstructor">s&lt;s</a> <a id="16669" class="Symbol">:</a> <a id="16671" class="Symbol">∀</a> <a id="16673" class="Symbol">{</a><a id="16674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16674" class="Bound">m</a> <a id="16676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16676" class="Bound">n</a> <a id="16678" class="Symbol">:</a> <a id="16680" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16681" class="Symbol">}</a> <a id="16683" class="Symbol">→</a> <a id="16685" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16674" class="Bound">m</a> <a id="16687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16606" class="Datatype Operator">&lt;</a> <a id="16689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16676" class="Bound">n</a> <a id="16691" class="Symbol">→</a> <a id="16693" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16697" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16674" class="Bound">m</a> <a id="16699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16606" class="Datatype Operator">&lt;</a> <a id="16701" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16676" class="Bound">n</a>{% endraw %}</pre>
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
*irreflexive* in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
*trichotomy*: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly where `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred
to the chapter that introduces [negation]({{ site.baseurl }}{% link out/plfa/Negation.md %}).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by directly
exploiting the corresponding properties of inequality.

### Exercise (`<-trans`)

Show that strict inequality is transitive.

### Exercise (`trichotomy`) {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
* `m < n`,
* `m ≡ n`, or
* `m > n`
This only involves two relations, as we define `m > n` to
be the same as `n < m`. You will need a suitable data declaration,
similar to that used for totality.  (We will show that the three cases
are exclusive after [negation]({{ site.baseurl }}{% link out/plfa/Negation.md %}) is introduced.)

### Exercise (`+-mono-<`)

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

### Exercise (`≤-implies-<`, `<-implies-≤`)

Show that `suc m ≤ n` implies `m < n`, and conversely.

### Exercise (`<-trans′`)

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.


## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are *binary relations*, while even and odd are
*unary relations*, sometimes called *predicates*.
<pre class="Agda">{% raw %}<a id="19090" class="Keyword">data</a> <a id="even"></a><a id="19095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19095" class="Datatype">even</a> <a id="19100" class="Symbol">:</a> <a id="19102" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="19104" class="Symbol">→</a> <a id="19106" class="PrimitiveType">Set</a>
<a id="19110" class="Keyword">data</a> <a id="odd"></a><a id="19115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19115" class="Datatype">odd</a>  <a id="19120" class="Symbol">:</a> <a id="19122" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="19124" class="Symbol">→</a> <a id="19126" class="PrimitiveType">Set</a>

<a id="19131" class="Keyword">data</a> <a id="19136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19095" class="Datatype">even</a> <a id="19141" class="Keyword">where</a>
  <a id="even.zero"></a><a id="19149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19149" class="InductiveConstructor">zero</a> <a id="19154" class="Symbol">:</a> <a id="19156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19095" class="Datatype">even</a> <a id="19161" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="even.suc"></a><a id="19168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19168" class="InductiveConstructor">suc</a>  <a id="19173" class="Symbol">:</a> <a id="19175" class="Symbol">∀</a> <a id="19177" class="Symbol">{</a><a id="19178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19178" class="Bound">n</a> <a id="19180" class="Symbol">:</a> <a id="19182" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="19183" class="Symbol">}</a> <a id="19185" class="Symbol">→</a> <a id="19187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19115" class="Datatype">odd</a> <a id="19191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19178" class="Bound">n</a> <a id="19193" class="Symbol">→</a> <a id="19195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19095" class="Datatype">even</a> <a id="19200" class="Symbol">(</a><a id="19201" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="19205" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19178" class="Bound">n</a><a id="19206" class="Symbol">)</a>

<a id="19209" class="Keyword">data</a> <a id="19214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19115" class="Datatype">odd</a> <a id="19218" class="Keyword">where</a>
  <a id="odd.suc"></a><a id="19226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19226" class="InductiveConstructor">suc</a>   <a id="19232" class="Symbol">:</a> <a id="19234" class="Symbol">∀</a> <a id="19236" class="Symbol">{</a><a id="19237" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19237" class="Bound">n</a> <a id="19239" class="Symbol">:</a> <a id="19241" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="19242" class="Symbol">}</a> <a id="19244" class="Symbol">→</a> <a id="19246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19095" class="Datatype">even</a> <a id="19251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19237" class="Bound">n</a> <a id="19253" class="Symbol">→</a> <a id="19255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19115" class="Datatype">odd</a> <a id="19259" class="Symbol">(</a><a id="19260" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="19264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19237" class="Bound">n</a><a id="19265" class="Symbol">)</a>{% endraw %}</pre>
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

This is also our first use of *overloaded* constructors,
that is, using the same name for different constructors depending on
the context.  Here `suc` means one of three constructors:

    suc : `ℕ → `ℕ
    suc : ∀ {n : ℕ} → odd n → even (suc n)
    suc : ∀ {n : ℕ} → even n → odd (suc n)

Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.

We show that the sum of two even numbers is even.
<pre class="Agda">{% raw %}<a id="e+e≡e"></a><a id="20393" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20393" class="Function">e+e≡e</a> <a id="20399" class="Symbol">:</a> <a id="20401" class="Symbol">∀</a> <a id="20403" class="Symbol">{</a><a id="20404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20404" class="Bound">m</a> <a id="20406" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20406" class="Bound">n</a> <a id="20408" class="Symbol">:</a> <a id="20410" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20411" class="Symbol">}</a> <a id="20413" class="Symbol">→</a> <a id="20415" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19095" class="Datatype">even</a> <a id="20420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20404" class="Bound">m</a> <a id="20422" class="Symbol">→</a> <a id="20424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19095" class="Datatype">even</a> <a id="20429" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20406" class="Bound">n</a> <a id="20431" class="Symbol">→</a> <a id="20433" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19095" class="Datatype">even</a> <a id="20438" class="Symbol">(</a><a id="20439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20404" class="Bound">m</a> <a id="20441" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20443" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20406" class="Bound">n</a><a id="20444" class="Symbol">)</a>
<a id="o+e≡o"></a><a id="20446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20446" class="Function">o+e≡o</a> <a id="20452" class="Symbol">:</a> <a id="20454" class="Symbol">∀</a> <a id="20456" class="Symbol">{</a><a id="20457" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20457" class="Bound">m</a> <a id="20459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20459" class="Bound">n</a> <a id="20461" class="Symbol">:</a> <a id="20463" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20464" class="Symbol">}</a> <a id="20466" class="Symbol">→</a> <a id="20468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19115" class="Datatype">odd</a>  <a id="20473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20457" class="Bound">m</a> <a id="20475" class="Symbol">→</a> <a id="20477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19095" class="Datatype">even</a> <a id="20482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20459" class="Bound">n</a> <a id="20484" class="Symbol">→</a> <a id="20486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19115" class="Datatype">odd</a>  <a id="20491" class="Symbol">(</a><a id="20492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20457" class="Bound">m</a> <a id="20494" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="20496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20459" class="Bound">n</a><a id="20497" class="Symbol">)</a>

<a id="20500" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20393" class="Function">e+e≡e</a> <a id="20506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19149" class="InductiveConstructor">zero</a>     <a id="20515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20515" class="Bound">en</a>  <a id="20519" class="Symbol">=</a>  <a id="20522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20515" class="Bound">en</a>
<a id="20525" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20393" class="Function">e+e≡e</a> <a id="20531" class="Symbol">(</a><a id="20532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19168" class="InductiveConstructor">suc</a> <a id="20536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20536" class="Bound">om</a><a id="20538" class="Symbol">)</a> <a id="20540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20540" class="Bound">en</a>  <a id="20544" class="Symbol">=</a>  <a id="20547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19168" class="InductiveConstructor">suc</a> <a id="20551" class="Symbol">(</a><a id="20552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20446" class="Function">o+e≡o</a> <a id="20558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20536" class="Bound">om</a> <a id="20561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20540" class="Bound">en</a><a id="20563" class="Symbol">)</a>

<a id="20566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20446" class="Function">o+e≡o</a> <a id="20572" class="Symbol">(</a><a id="20573" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19226" class="InductiveConstructor">suc</a> <a id="20577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20577" class="Bound">em</a><a id="20579" class="Symbol">)</a> <a id="20581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20581" class="Bound">en</a>  <a id="20585" class="Symbol">=</a>  <a id="20588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19226" class="InductiveConstructor">suc</a> <a id="20592" class="Symbol">(</a><a id="20593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20393" class="Function">e+e≡e</a> <a id="20599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20577" class="Bound">em</a> <a id="20602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20581" class="Bound">en</a><a id="20604" class="Symbol">)</a>{% endraw %}</pre>
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

To show that the sum of two even numbers is even, consider the evidence that the
first number is even. If it is because it is zero, then the sum is even because the
second number is even.  If it is because it is the successor of an odd number,
then the result is even because it is the successor of the sum of an odd and an
even number, which is odd.

To show that the sum of an odd and even number is odd, consider the evidence
that the first number is odd. If it is because it is the successor of an even
number, then the result is odd because it is the successor of the sum of two
even numbers, which is even.

### Exercise (`o+o≡e`)

Show that the sum of two odd numbers is even.


<!--

## Formalising preorder

<pre class="Agda">{% raw %}<a id="21765" class="Keyword">record</a> <a id="IsPreorder"></a><a id="21772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21772" class="Record">IsPreorder</a> <a id="21783" class="Symbol">{</a><a id="21784" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21784" class="Bound">A</a> <a id="21786" class="Symbol">:</a> <a id="21788" class="PrimitiveType">Set</a><a id="21791" class="Symbol">}</a> <a id="21793" class="Symbol">(</a><a id="21794" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21794" class="Bound Operator">_≤_</a> <a id="21798" class="Symbol">:</a> <a id="21800" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21784" class="Bound">A</a> <a id="21802" class="Symbol">→</a> <a id="21804" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21784" class="Bound">A</a> <a id="21806" class="Symbol">→</a> <a id="21808" class="PrimitiveType">Set</a><a id="21811" class="Symbol">)</a> <a id="21813" class="Symbol">:</a> <a id="21815" class="PrimitiveType">Set</a> <a id="21819" class="Keyword">where</a>
  <a id="21827" class="Keyword">field</a>
    <a id="IsPreorder.reflexive"></a><a id="21837" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21837" class="Field">reflexive</a> <a id="21847" class="Symbol">:</a> <a id="21849" class="Symbol">∀</a> <a id="21851" class="Symbol">{</a><a id="21852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21852" class="Bound">x</a> <a id="21854" class="Symbol">:</a> <a id="21856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21784" class="Bound">A</a><a id="21857" class="Symbol">}</a> <a id="21859" class="Symbol">→</a> <a id="21861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21852" class="Bound">x</a> <a id="21863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21794" class="Bound Operator">≤</a> <a id="21865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21852" class="Bound">x</a>
    <a id="IsPreorder.trans"></a><a id="21871" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21871" class="Field">trans</a> <a id="21877" class="Symbol">:</a> <a id="21879" class="Symbol">∀</a> <a id="21881" class="Symbol">{</a><a id="21882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21882" class="Bound">x</a> <a id="21884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21884" class="Bound">y</a> <a id="21886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21886" class="Bound">z</a> <a id="21888" class="Symbol">:</a> <a id="21890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21784" class="Bound">A</a><a id="21891" class="Symbol">}</a> <a id="21893" class="Symbol">→</a> <a id="21895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21882" class="Bound">x</a> <a id="21897" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21794" class="Bound Operator">≤</a> <a id="21899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21884" class="Bound">y</a> <a id="21901" class="Symbol">→</a> <a id="21903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21884" class="Bound">y</a> <a id="21905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21794" class="Bound Operator">≤</a> <a id="21907" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21886" class="Bound">z</a> <a id="21909" class="Symbol">→</a> <a id="21911" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21882" class="Bound">x</a> <a id="21913" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21794" class="Bound Operator">≤</a> <a id="21915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21886" class="Bound">z</a>

<a id="IsPreorder-≤"></a><a id="21918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21918" class="Function">IsPreorder-≤</a> <a id="21931" class="Symbol">:</a> <a id="21933" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21772" class="Record">IsPreorder</a> <a id="21944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1205" class="Datatype Operator">_≤_</a>
<a id="21948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21918" class="Function">IsPreorder-≤</a> <a id="21961" class="Symbol">=</a>
  <a id="21965" class="Keyword">record</a>
    <a id="21976" class="Symbol">{</a> <a id="21978" class="Field">reflexive</a> <a id="21988" class="Symbol">=</a> <a id="21990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5710" class="Function">≤-refl</a>
    <a id="22001" class="Symbol">;</a> <a id="22003" class="Field">trans</a> <a id="22009" class="Symbol">=</a> <a id="22011" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6374" class="Function">≤-trans</a>
    <a id="22023" class="Symbol">}</a>{% endraw %}</pre>

-->


## Standard prelude

Definitions similar to those in this chapter can be found in the standard library.
<pre class="Agda">{% raw %}<a id="22160" class="Keyword">import</a> <a id="22167" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="22176" class="Keyword">using</a> <a id="22182" class="Symbol">(</a><a id="22183" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#802" class="Datatype Operator">_≤_</a><a id="22186" class="Symbol">;</a> <a id="22188" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#833" class="InductiveConstructor">z≤n</a><a id="22191" class="Symbol">;</a> <a id="22193" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#875" class="InductiveConstructor">s≤s</a><a id="22196" class="Symbol">)</a>
<a id="22198" class="Keyword">import</a> <a id="22205" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="22225" class="Keyword">using</a> <a id="22231" class="Symbol">(</a><a id="22232" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1902" class="Function">≤-refl</a><a id="22238" class="Symbol">;</a> <a id="22240" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2095" class="Function">≤-trans</a><a id="22247" class="Symbol">;</a> <a id="22249" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1952" class="Function">≤-antisym</a><a id="22258" class="Symbol">;</a> <a id="22260" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2207" class="Function">≤-total</a><a id="22267" class="Symbol">;</a>
                                  <a id="22303" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#11056" class="Function">+-monoʳ-≤</a><a id="22312" class="Symbol">;</a> <a id="22314" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10966" class="Function">+-monoˡ-≤</a><a id="22323" class="Symbol">;</a> <a id="22325" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10810" class="Function">+-mono-≤</a><a id="22333" class="Symbol">)</a>{% endraw %}</pre>
In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in Chapter [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md %})),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here
as well as taking as implicit arguments that here are explicit.

## Unicode

This chapter uses the following unicode.

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.

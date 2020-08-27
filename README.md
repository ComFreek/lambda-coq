# Lambda Calculus in Coq

**A from-scratch formalization of [untyped lambda calculus](https://en.wikipedia.org/wiki/Lambda_calculus) with [de Bruijn indices](https://en.wikipedia.org/wiki/De_Bruijn_index) in [Coq](https://coq.inria.fr/)+[SSReflect](https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html).**

With this project, I try to brush up my Coq knowledge and learn more about how de Bruijn indices are implemented. Last time, in [my formalization of a basic ontology language](https://github.com/ComFreek/basic-ontology-language) I learned the hard way that named variables are perhaps not that easy as on pen & paper. Hence, this time I am trying de Bruijn indices from the start.

In `utlc.v` we start off pretty easy with

```coq
(* Untyped LC (UTLC) *)
Inductive LC :=
  | var: nat -> LC
  | app: LC -> LC -> LC
  | lam: LC -> LC
.
```

Then, we

- formalize the notions of closed terms and beta reduction (e.g. to prove `forall s t, (\ \ #1) s t -->* s`),
- define an internalization `[[-]]` of Coq-level lambda terms into lambda-level terms (Church encoding) and subsequently define an evaluator term `f` such that `f [[x]] -->* x`,
- and in `dtlc.v` (*dependently typed LC*) define a type system.

The evaluator is due <insert other person's name here after I received permission to do so>.

## Status

In development. Suggestions welcome!
# Lambda Calculus in Coq

**A from-scratch formalization of [untyped lambda calculus](https://en.wikipedia.org/wiki/Lambda_calculus) with [de Bruijn indices](https://en.wikipedia.org/wiki/De_Bruijn_index) in [Coq](https://coq.inria.fr/)+[SSReflect](https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html).**

With this project, I try to brush up my Coq knowledge and learn more about how de Bruijn indices are implemented. Last time, in [my formalization of a basic ontology language](https://github.com/ComFreek/basic-ontology-language) I learned the hard way that named variables are perhaps not that easy as on pen & paper. Hence, this time I am trying de Bruijn indices from the start.

We start off easy with

```coq
Inductive LC :=
  | var: nat -> LC
  | app: LC -> LC -> LC
  | lam: LC -> LC
.
```

Then, we

- formalize the notion of closed terms and beta reduction,
- prove `forall s t, (\ \ #1) s t -->* s` (sanity check!),
- define an internalization `[[-]]` of Coq-level lambda terms into lambda-level terms (Church encoding),
- and finally define an evaluator term `f` such that `f [[x]] -->* x`.

The evaluator is due <insert other person's name here after I received permission to do so>.

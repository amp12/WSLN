# WSLN 

### [github.com/amp12/WSLN](https://github.com/amp12/WSLN)

`adgda/WSLN` is an Agda library for the well-scoped version of the locally nameless method of representing syntax. The library is parameterised by a Plotkin-style binding signature and makes use of some  (more or less) standard library definitions in `agda/Prelude`. 
  
`agda/Adequacy` gives a proof of the adequacy of this style of representation with respect to naïve nameful syntax modulo α-conversion 


### [Browsable code](https://amp12.github.io/WSLN/html/README.html)

Checked with Agda version 2.8.0 using flags
  `--safe`
  `--without-K`
  
### [Accompanying paper](https://arxiv.org/abs/2605.08990)

When using interactive theorem provers based on dependent type theory to define and reason about languages involving binding constructs, we advocate the use of a well-scoped version of the locally nameless method of representing syntax. This paper describes generic code parameterized by a Plotkin-style binding signature for this style of syntax representation within the Agda theorem prover, gives a proof of its adequacy with respect to naive nameful syntax modulo alpha-conversion and discusses some examples of its use.

### Examples of using the WSLN library

* Examples of binding signatures: [untyped λ-calculus](https://github.com/amp12/WSLN/blob/main/agda/Lambda.agda), [π-calculus](https://github.com/amp12/WSLN/blob/main/agda/PiCalc.agda) 
 
*  [Martin-Löf Type Theory](https://github.com/amp12/WSLN/blob/main/agda/MLTT.agda) with countably many Agda-style non-cumulative universes closed under Pi-types, natural number type and intensional identity types.

*  [Gödel's System T](https://github.com/amp12/WSLN/blob/main/agda/GST.agda). Decidability of βη-conversion using well-scoped locally nameless syntax, proved via a normalization by evaluation argument, in safe Agda.

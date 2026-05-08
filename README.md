# WSLN

`adgda/WSLN` is an Agda library for the well-scoped version of the locally nameless method of representing syntax. The library is parameterised by a Plotkin-style binding signature and makes use of some  (more or less) standard library definitions in `agda/Prelude`. 
  
`agda/Adequacy` gives a proof of the adequacy of this style of representation with respect to naïve nameful syntax modulo α-conversion 
 
Examples of WSLN in use:
 
*  `agda/MLTT` Martin-Löf Type Theory with countably many Agda-style non-cumulative universes closed under Pi-types, natural number type and intensional identity types.
*  `agda/GST` Decidability of βη-conversion for Gödel's System T using well-scoped locally nameless syntax, proved via a normalization by evaluation argument, in safe Agda.
* Further examples of binding signatures: untyped λ-calculus (`agda/Lambda.agda`), π-calculus (`agda/PiCalc.agda`)




Checked with Agda version 2.8.0 using flags
  --safe
  --without-K

© Andrew Pitts 2026 
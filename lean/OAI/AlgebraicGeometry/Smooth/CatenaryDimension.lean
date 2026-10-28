/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
This file has been modified.
-/
import OAI.AlgebraicGeometry.Cycle.SupportEq
import OAI.Algebra.RingTheory.TranscendenceDegreeKrullDimension
import OAI.AlgebraicGeometry.Cycle.ComponentDimension
import OAI.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
import OAI.AlgebraicGeometry.Smooth.DimensionFormula
import OAI.AlgebraicGeometry.Smooth.PointwiseDimension
import OAI.CategoryTheory.ConcreteCategory.Notation
import OAI.Algebra.Foundations.PolynomialCatenaryT
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Catenary Dimension -/

namespace OAI.AlgebraicGeometry.Smooth.CatenaryDimension.RingHom

noncomputable section

open _root_.RingHom

/-!
# Catenary dimension formulas for smooth complex schemes

This file proves the arbitrary-dimensional pointwise dimension formula for smooth complex
schemes. Its commutative-algebra bridge is
`HodgeConjecture.Lemmas.RingTheory.TranscendenceDegreeKrullDimension`, which compares quotient
dimensions under a quasi-finite map of finite-type algebras, using Noether normalization and the
finite extension of residue fields.

Applied to the étale polynomial coordinates of a standard-smooth algebra, the bridge transfers
the arbitrary-prime polynomial dimension formula. An affine neighborhood then supplies enough
specialization chains to prove `height x + coheight x = d` at every point of a smooth complex
`d`-fold. Consequently, the reduced closure of a point of coheight `p` has dimension `d - p`.
-/

open _root_.CategoryTheory _root_.Ideal _root_.MvPolynomial _root_.Topology

/-- For every prime of a standard-smooth complex algebra of relative dimension `d`, its height
plus the dimension of its quotient is `d`. -/
lemma IsStandardSmoothOfRelativeDimension.height_add_ringKrullDim_quotient_eq_complex
    {S : Type} [CommRing S] {f : ℂ →+* S} {d : ℕ}
    (hf : f.IsStandardSmoothOfRelativeDimension d)
    (P : Ideal S) [P.IsPrime] :
    (↑P.height : WithBot ℕ∞) + ringKrullDim (S ⧸ P) = d := by
  obtain ⟨g, hgC, hg⟩ := hf.exists_etale_mvPolynomial
  let : Algebra ℂ S := f.toAlgebra
  let : Algebra (MvPolynomial (Fin d) ℂ) S := g.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) S :=
    IsScalarTower.of_algebraMap_eq' hgC.symm
  let : Algebra.Etale (MvPolynomial (Fin d) ℂ) S :=
    RingHom.etale_algebraMap.mp hg
  let : Algebra.FiniteType ℂ S :=
    Algebra.FiniteType.trans (R := ℂ) (S := MvPolynomial (Fin d) ℂ)
      (A := S) inferInstance inferInstance
  have hheight : P.height = (P.under (MvPolynomial (Fin d) ℂ)).height :=
    OAI.Algebra.RingTheory.SmoothKrullDimension.QuasiFinite.height_eq_height_under P
  have hquot : ringKrullDim (S ⧸ P) =
      ringKrullDim (MvPolynomial (Fin d) ℂ ⧸ P.under (MvPolynomial (Fin d) ℂ)) :=
    OAI.Algebra.RingTheory.TranscendenceDegreeKrullDimension.QuasiFinite.ringKrullDim_quotient_eq
      (k := ℂ) (R := MvPolynomial (Fin d) ℂ) P
  rw [hheight, hquot]
  exact OAI.Algebra.Foundations.PolynomialCatenaryT.PolynomialCatenary.MvPolynomial.height_add_ringKrullDim_quotient_eq_fin
    (P.under (MvPolynomial (Fin d) ℂ))

end

end OAI.AlgebraicGeometry.Smooth.CatenaryDimension.RingHom

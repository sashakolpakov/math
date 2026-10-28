import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.AffineMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoefficientPointEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.AffineTerms
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.IntrinsicSquare

/-! # Point Pullback -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.PointPullback

noncomputable section

/-! On actual affine projective charts, the fixed common-refinement
dual map is the canonical Ext map of the original coefficient morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps

variable (M M' : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] [M'.IsQuasicoherent] [M'.IsFiniteType]
  (j : σ) (B b : ℕ) (hb : b ≤ B) (f : M ⟶ M')
  (U : (Proj (homogeneousSubmodule σ R)).Opens) (hU : IsAffineOpen U)
  (k : σ) (hUk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
  (Q : Type u) [CommRing Q] [Algebra Γ(Proj (homogeneousSubmodule σ R), U) Q]
  (C : Type u) [AddCommGroup C] [Module Q C] [Module Γ(Proj (homogeneousSubmodule σ R), U) C]
  [IsScalarTower Γ(Proj (homogeneousSubmodule σ R), U) Q C]
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(Proj (homogeneousSubmodule σ R), U) Q)
  (eC : (AffineOpen.InternalHom.sections U hU).obj M' ≅ ModuleCat.of Γ(Proj (homogeneousSubmodule σ R), U) C)
  (x : C)
  (hv : (AffineOpen.InternalHom.sections U hU).map f ≫ eC.hom = eM.hom ≫
    Quotient.CoefficientEvaluation.point Γ(Proj (homogeneousSubmodule σ R), U) Q C x)

 theorem inverse_eq {A : Type u} [CommRing A] {V W : ModuleCat.{u} A}
    (e : V ≅ W) {v : V} {w : W} (h : e.hom v = w) : e.inv w = v := by
  rw [← h]
  exact Iso.hom_inv_id_apply e v

include hb k hUk hv in
abbrev pullback (n : ℕ)
    (z : Γ(((DualMap.dualFunctor (R := R) j b).obj
      (.op (IntegralComparison.Projective.NegativeResolution.complex M' j B))).homology n, U)) := by
  let N := AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b
  let K := IntegralComparison.Projective.NegativeResolution.complex M j B
  let L := IntegralComparison.Projective.NegativeResolution.complex M' j B
  letI : N.IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j b)
  letI (q : ℕ) : (K.X q).IsQuasicoherent := AffineTerms.fixed_qc M j B q
  letI (q : ℕ) : (L.X q).IsQuasicoherent := AffineTerms.fixed_qc M' j B q
  letI (q : ℕ) : ((Affine.LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent :=
    AffineTerms.fixed_dual_qc M j B b hb q
  letI (q : ℕ) : ((Affine.LinearResolutionPurity.internalComplex N L).X q).IsQuasicoherent :=
    AffineTerms.fixed_dual_qc M' j B b hb q
  letI (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q)) :=
    AffineTerms.fixed_projective M j B U hU k hUk q
  letI (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj (L.X q)) :=
    AffineTerms.fixed_projective M' j B U hU k hUk q
  exact inverse_eq (AffinePrincipal.Cohomology.Comparison.comparison U hU N K n)
    (AffineMap.comparison M M' j B b hb f U hU k hUk _ _ eM eC
      (Quotient.CoefficientEvaluation.point Γ(Proj (homogeneousSubmodule σ R), U) Q C x) hv n z)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.PointPullback

import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.RefinementCoefficientEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.AffineTerms
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.IntrinsicSquare

/-! # Affine Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.AffineMap

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
  (D D' : ModuleCat Γ(Proj (homogeneousSubmodule σ R), U))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ D) (eM' : (AffineOpen.InternalHom.sections U hU).obj M' ≅ D')
  (v : D ⟶ D') (hv : (AffineOpen.InternalHom.sections U hU).map f ≫ eM'.hom = eM.hom ≫ v)

include hb k hUk hv in
abbrev comparison (n : ℕ)
    (z : Γ(((DualMap.dualFunctor (R := R) j b).obj
      (.op (IntegralComparison.Projective.NegativeResolution.complex M' j B))).homology n, U)) := by
  let N := AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b
  let K := IntegralComparison.Projective.NegativeResolution.complex M j B
  let L := IntegralComparison.Projective.NegativeResolution.complex M' j B
  let P := IntegralComparison.Projective.NegativeRefinement.complex M M' j B f
  letI : N.IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j b)
  letI (q : ℕ) : (K.X q).IsQuasicoherent := AffineTerms.fixed_qc M j B q
  letI (q : ℕ) : (L.X q).IsQuasicoherent := AffineTerms.fixed_qc M' j B q
  letI (q : ℕ) : (P.X q).IsQuasicoherent := AffineTerms.common_qc M M' j B f q
  letI (q : ℕ) : ((Affine.LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent :=
    AffineTerms.fixed_dual_qc M j B b hb q
  letI (q : ℕ) : ((Affine.LinearResolutionPurity.internalComplex N L).X q).IsQuasicoherent :=
    AffineTerms.fixed_dual_qc M' j B b hb q
  letI (q : ℕ) : ((Affine.LinearResolutionPurity.internalComplex N P).X q).IsQuasicoherent :=
    AffineTerms.common_dual_qc M M' j B b hb f q
  letI (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q)) :=
    AffineTerms.fixed_projective M j B U hU k hUk q
  letI (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj (L.X q)) :=
    AffineTerms.fixed_projective M' j B U hU k hUk q
  letI (q : ℕ) : Projective ((AffineOpen.InternalHom.sections U hU).obj (P.X q)) :=
    AffineTerms.common_projective M M' j B f U hU k hUk q
  exact Affine.RefinementCoefficientEvaluation.comparison U hU N K L P M M'
    (IntegralComparison.Projective.NegativeResolution.augmentation M j B)
    (IntegralComparison.Projective.NegativeResolution.augmentation M' j B)
    (IntegralComparison.Projective.NegativeRefinement.augmentation M M' j B f)
    D D' eM eM' f (IntegralComparison.Projective.NegativeRefinement.leftHom M M' j B f).chainMap
    (IntegralComparison.Projective.NegativeRefinement.rightHom M M' j B f).chainMap
    (IntegralComparison.Projective.NegativeRefinement.left_augmentation M M' j B f)
    (IntegralComparison.Projective.NegativeRefinement.right_augmentation M M' j B f) v hv n
    (DualMap.map M M' j B b hb f n)
    (IntrinsicSquare.Intrinsic.square M M' j B b hb f n) z

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.AffineMap

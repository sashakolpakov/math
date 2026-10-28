import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FiniteProjectivePurity

/-! # Coefficient Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.CoefficientPurity

noncomputable section

/-! An actual projective resolution of the zero coefficient module
has zero ordinary-Hom cohomology, including on native affine sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientEvaluation

theorem cohomology (R : Type u) [CommRing R] (M N : ModuleCat.{u} R)
    (P : ProjectiveResolution M) (hM : IsZero M) (n : ℕ) : IsZero (Quotient.CoefficientEvaluation.group R N n P) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  have h := congrArg (fun f => Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R N) P P f n) (hM.eq_of_src (𝟙 M) 0)
  simpa only [Resolution.CohomologyMaps.map_id, Resolution.CohomologyMaps.map_zero] using h

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.LinearHom
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) (K : ChainComplex X.Modules ℕ)
  [∀ i, (K.X i).IsQuasicoherent]
  (M : X.Modules) [M.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  [∀ i, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X i))]
  (C : Type u) [AddCommGroup C] [Module Γ(X, U) C]
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(X, U) C)

include ε eM in
theorem linear_exactAt (hC : IsZero (ModuleCat.of Γ(X, U) C)) (n : ℕ) :
    ((((AffineOpen.LinearHom.sectionHom U N).mapHomologicalComplex (ComplexShape.down ℕ).symm).obj K.op)).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply (HomologicalComplex.homologyMapIso
    (Affine.LinearResolutionPurity.sectionComplexIso U hU N K) n).isZero_iff.mpr
  exact cohomology Γ(X, U) (ModuleCat.of Γ(X, U) C) ((AffineOpen.InternalHom.sections U hU).obj N)
    (Affine.FiniteProjectivePurity.resolution U hU K M ε C eM) hC n

include ε eM in
theorem exactAt (hC : IsZero (ModuleCat.of Γ(X, U) C)) (n : ℕ) :
    (Affine.LocalExactness.sectionComplex
      (Affine.LinearResolutionPurity.internalComplex N K) U).ExactAt n := by
  let J := (((AffineOpen.LinearHom.sectionHom U N).mapHomologicalComplex (ComplexShape.down ℕ).symm).obj K.op)
  have h : J.ExactAt n := linear_exactAt U hU N K M ε C eM hC n
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h ⊢
  let G := forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat
  exact ((J.sc n).mapHomologyIso G).isZero_iff.mpr (G.map_isZero h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.CoefficientPurity

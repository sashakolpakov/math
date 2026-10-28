import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FixedFrameAuxiliaryFamily
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices

/-! # Fixed Frame Rational Conjugation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FixedFrameRationalConjugation.CM

noncomputable section

/-! The specified source trace frame identifies the q-adic projection
of any actual rational Weil lift with its simultaneous unitary blocks.
Only equality of its concrete symplectic projection is required. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices.Local

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n)

def blocks (g : D.RationalSU) : Fin s → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q :=
  fun i => Matrix.SpecialLinearGroup.map (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (i, false)) g.val

theorem conjugation (u : MpF)
    (hu : FixedFrameAuxiliaryFamily.CM.Family.CoordinateIdentity E D e u) (g : D.RationalSU)
    (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin s × Fin 3) ℚ) (hγ : γ.val = CMExtraction.RationalPhaseColumn.Intrinsic.rationalUnitaryMatrix E D.pel.reference e g) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom
      (D.weil.finite.project (u * D.weil.finiteLift γ * u⁻¹)) = CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c (blocks E D g) := by
  obtain ⟨S, hS, hphase⟩ := hu
  rw [RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finite_coordinate_conjugation_projection q D.weil S u hS]
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (S.val * (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ).val * (S⁻¹).val) *ᵥ x = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change S.val *ᵥ (γ.val.map (algebraMap ℚ ℚ_[q]) *ᵥ ((S⁻¹).val *ᵥ x)) = _
  rw [hγ, hphase]
  have hs : S.val *ᵥ ((S⁻¹).val *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, ← Submonoid.coe_mul, mul_inv_cancel,
      OneMemClass.coe_one, Matrix.one_mulVec]
  rw [hs]
  funext i
  cases i with
  | inl p => exact (CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic_inl c (blocks E D g) x p.1 p.2).symm
  | inr p => exact (CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic_inr c (blocks E D g) x p.1 p.2).symm

theorem actual_lift_conjugation (u : MpF)
    (hu : FixedFrameAuxiliaryFamily.CM.Family.CoordinateIdentity E D e u) (g : D.RationalSU)
    (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin s × Fin 3) ℚ) (hγ : γ.val = CMExtraction.RationalPhaseColumn.Intrinsic.rationalUnitaryMatrix E D.pel.reference e g)
    (m : MpF) (hm : D.weil.finite.project m = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) γ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom
      (D.weil.finite.project (u * m * u⁻¹)) = CMExtraction.BlockFamilyMatrices.Local.blockFamilySymplectic c (blocks E D g) := by
  have he : D.weil.finite.project (u * m * u⁻¹) =
      D.weil.finite.project (u * D.weil.finiteLift γ * u⁻¹) := by
    simp only [map_mul, map_inv, hm, D.weil.finiteLift_covers]
  rw [he]
  exact conjugation E D e c u hu g γ hγ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FixedFrameRationalConjugation.CM

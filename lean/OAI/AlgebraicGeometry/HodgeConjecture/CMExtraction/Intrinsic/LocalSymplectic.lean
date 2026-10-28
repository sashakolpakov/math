import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteDilation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices

/-! # Local Symplectic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalSymplectic

noncomputable section

/-! The retained native coordinate witness identifies the actual q-adic
projection of every rational finite Weil operator with the simultaneous
inverse-transpose position blocks. -/

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices.Local
open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (v : Multiplicity.Odd.Sign E)
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n)

def nativeLocalUnitaryBlocks (g : D.RationalSU) : Fin s → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q :=
  fun i => Matrix.SpecialLinearGroup.map (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (i, false)) g.val

theorem native_local_symplectic_conjugation (u : MpF)
    (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u) (g : D.RationalSU) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom
      (D.weil.finite.project (u * D.weil.finiteLift (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E D.pel.reference e v he g) * u⁻¹)) =
        BlockFamilyMatrices.Local.blockFamilySymplectic c (nativeLocalUnitaryBlocks E D g) := by
  obtain ⟨S, hS, hphase⟩ := hu
  rw [RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finite_coordinate_conjugation_projection q D.weil S u hS]
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (S.val * (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q])
    (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E D.pel.reference e v he g)).val * (S⁻¹).val) *ᵥ x = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change S.val *ᵥ ((RationalPhaseColumn.Intrinsic.rationalUnitaryMatrix E D.pel.reference e g).map (algebraMap ℚ ℚ_[q]) *ᵥ
    ((S⁻¹).val *ᵥ x)) = _
  rw [hphase]
  have hs : S.val *ᵥ ((S⁻¹).val *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, ← Submonoid.coe_mul, mul_inv_cancel,
      OneMemClass.coe_one, Matrix.one_mulVec]
  rw [hs]
  funext i
  cases i with
  | inl p => exact (BlockFamilyMatrices.Local.blockFamilySymplectic_inl c (nativeLocalUnitaryBlocks E D g) x p.1 p.2).symm
  | inr p => exact (BlockFamilyMatrices.Local.blockFamilySymplectic_inr c (nativeLocalUnitaryBlocks E D g) x p.1 p.2).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalSymplectic

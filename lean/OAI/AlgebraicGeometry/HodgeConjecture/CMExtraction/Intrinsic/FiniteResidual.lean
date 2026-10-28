import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalSymplectic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyLift
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.Sl
import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePadicCommutation

/-! # Finite Residual -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteResidual

noncomputable section

/-! Factor the native rational finite Weil operator into its explicit
local block lift and a residual operator with trivial q-adic projection.
The residual commutes exactly with every active local SL3 lift. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.FinitePadicCommutation.Realization
open scoped Classical _root_.Matrix

namespace Local

theorem activeFiniteLift_commute_of_trivial_projection
    (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
    {n : ℕ} (c : (Place × Fin 3) ≃ Fin n) (μ : Place)
    {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA) (m : MpF)
    (hm : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom (D.finite.project m) = 1) :
    ∀ g, Commute m (ActiveLocalLift.activeFiniteLift q c μ D g) := by
  apply Finite.Sl.Local.finite_sl3_lift_commute q D
  intro g
  rw [ActiveLocalLift.activeFiniteLift_projection]
  apply Commute.symm
  apply RepresentationTheory.Hecke.RadialDilation.FinitePadicCommutation.Realization.finitePadicSymplecticInclusion_commute
  rw [hm]
  exact Commute.one_right _

end Local

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
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)

def nativeAwayResidual (g : D.RationalSU) : MpF :=
  (u * D.weil.finiteLift (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E D.pel.reference e v he g) * u⁻¹) *
    (BlockFamilyLift.Local.blockFamilyFiniteLift q c D.weil (fun τ => Contragredient.Local.contragredient ℚ_[q] (LocalSymplectic.nativeLocalUnitaryBlocks E D g τ)))⁻¹

theorem nativeAwayResidual_projection (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)
    (g : D.RationalSU) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom
      (D.weil.finite.project (nativeAwayResidual E D e v he c u g)) = 1 := by
  unfold nativeAwayResidual
  rw [D.weil.finite.project.map_mul, D.weil.finite.project.map_inv, map_mul, map_inv,
    LocalSymplectic.native_local_symplectic_conjugation E D e v he c u hu,
    BlockFamilyLift.Local.blockFamilyFiniteLift_dual_projection, mul_inv_cancel]

theorem nativeAwayResidual_factorization (g : D.RationalSU) :
    nativeAwayResidual E D e v he c u g *
      BlockFamilyLift.Local.blockFamilyFiniteLift q c D.weil (fun τ => Contragredient.Local.contragredient ℚ_[q] (LocalSymplectic.nativeLocalUnitaryBlocks E D g τ)) =
      u * D.weil.finiteLift (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E D.pel.reference e v he g) * u⁻¹ := by
  exact inv_mul_cancel_right _ _

theorem nativeAwayResidual_commute (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)
    (g : D.RationalSU) (μ : Fin s) :
    ∀ h, Commute (nativeAwayResidual E D e v he c u g) (ActiveLocalLift.activeFiniteLift q c μ D.weil h) :=
  Local.activeFiniteLift_commute_of_trivial_projection q c μ D.weil _
    (nativeAwayResidual_projection E D e v he c u hu g)

theorem nativeAwayResidual_other_prime (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)
    (g : D.RationalSU) (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom
      (D.weil.finite.project (nativeAwayResidual E D e v he c u g)) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[p]) (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E D.pel.reference e v he g) := by
  obtain ⟨S, hS, _⟩ := hu
  unfold nativeAwayResidual
  simp only [map_mul, map_inv]
  rw [hS, BlockFamilyLift.Local.blockFamilyFiniteLift_projection, D.weil.finiteLift_covers]
  simp only [RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic, MonoidHom.comp_apply,
    RepresentationTheory.Hecke.RadialDilation.FinitePadicOtherPrime.Realization.finitePadicSymplecticInclusion_other_prime q p hpq,
    RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.rationalSymplectic_finite_projection, inv_one, one_mul, mul_one]

theorem nativeAwayResidual_action (g : D.RationalSU) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) :
    D.weil.finiteAction (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E D.pel.reference e v he g)
        (D.weil.finite.action u⁻¹ f) =
      D.weil.finite.action u⁻¹
        (D.weil.finite.action (nativeAwayResidual E D e v he c u g)
          (D.weil.finite.action (BlockFamilyLift.Local.blockFamilyFiniteLift q c D.weil
            (fun τ => Contragredient.Local.contragredient ℚ_[q] (LocalSymplectic.nativeLocalUnitaryBlocks E D g τ))) f)) := by
  have h : D.weil.finiteLift (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E D.pel.reference e v he g) * u⁻¹ =
      u⁻¹ * (nativeAwayResidual E D e v he c u g * BlockFamilyLift.Local.blockFamilyFiniteLift q c D.weil
        (fun τ => Contragredient.Local.contragredient ℚ_[q] (LocalSymplectic.nativeLocalUnitaryBlocks E D g τ))) := by
    rw [nativeAwayResidual_factorization]
    group
  change D.weil.finite.action (D.weil.finiteLift _) (D.weil.finite.action u⁻¹ f) = _
  simp only [← LinearEquiv.mul_apply, ← map_mul]
  rw [h]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteResidual

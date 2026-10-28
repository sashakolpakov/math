import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveBlockMatrices
import OAI.RepresentationTheory.Hecke.RadialDilation.ActivePrimeSubstitution

/-! # Active Local Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveLocalLift

noncomputable section

/-! The active determinant-one block has an exact homomorphic lift into
the finite Weil cover, acting by ordinary substitution with no phase. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.Cm OAI.RepresentationTheory.Hecke.RadialDilation.ActivePrimeSubstitution.Realization
open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (e : (Place × Fin 3) ≃ Fin n) (μ : Place)

local instance localMeasurable : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance localBorel : BorelSpace ℚ_[q] := ⟨rfl⟩

def activeMetaplectic (ψ : AddChar ℚ_[q] ℂ) : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q →* RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ where
  toFun g := RepresentationTheory.Weil.Local.SpecialLinearCommutators.Construction.specialLinearMetaplectic (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) ψ
    (ActiveBlockMatrices.Local.activeBlockGL e μ g) (ActiveBlockMatrices.Local.activeBlockGL_det e μ g)
  map_one' := by
    apply Subtype.ext
    change RepresentationTheory.Weil.Local.LinearIntertwiner.Construction.linearOscillator ψ (ActiveBlockMatrices.Local.activeBlockGL e μ 1) = 1
    rw [map_one]
    exact RepresentationTheory.Weil.Local.LinearOscillatorHom.Construction.linearOscillator_one n ψ
  map_mul' g h := by
    apply Subtype.ext
    change RepresentationTheory.Weil.Local.LinearIntertwiner.Construction.linearOscillator ψ (ActiveBlockMatrices.Local.activeBlockGL e μ (g * h)) =
      RepresentationTheory.Weil.Local.LinearIntertwiner.Construction.linearOscillator ψ (ActiveBlockMatrices.Local.activeBlockGL e μ g) * RepresentationTheory.Weil.Local.LinearIntertwiner.Construction.linearOscillator ψ (ActiveBlockMatrices.Local.activeBlockGL e μ h)
    rw [map_mul, RepresentationTheory.Weil.Local.LinearOscillatorHom.Construction.linearOscillator_mul]

variable {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)

def activeFiniteLift : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q →* MpF :=
  (RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift q e D).comp (activeMetaplectic q e μ (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D))

theorem activeFiniteLift_projection (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    D.finite.project (activeFiniteLift q e μ D g) =
      RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic (ActiveBlockMatrices.Local.activeBlockGL e μ g)) :=
  (RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift_spec q e D _).1

theorem activeFiniteLift_full_substitution (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3)) (x : Place × Fin 3 → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (D.finite.action (activeFiniteLift q e μ D g) f).val x =
      f.val ((RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeChart q e).symm
        ((ActiveBlockMatrices.Local.activeBlockGL e μ g)⁻¹.val *ᵥ RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeProjection q e x, RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q x)) := by
  change (D.finite.action (RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift q e D
    (activeMetaplectic q e μ (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D) g)) f).val x = _
  rw [(RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift_spec q e D
    (activeMetaplectic q e μ (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D) g)).2]
  have hU : ∀ f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n, ∀ y,
      (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D)
        (activeMetaplectic q e μ (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D) g) f).val y =
        (1 : ℂ) * f.val ((ActiveBlockMatrices.Local.activeBlockGL e μ g)⁻¹.val *ᵥ y) := by
    intro f y
    rw [one_mul]
    exact RepresentationTheory.Weil.Local.SpecialLinearCommutators.Construction.specialLinearMetaplectic_apply (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D)
      (ActiveBlockMatrices.Local.activeBlockGL e μ g) (ActiveBlockMatrices.Local.activeBlockGL_det e μ g) f y
  simpa only [one_mul] using RepresentationTheory.Hecke.RadialDilation.IndexedPrimeSubstitution.Realization.indexedPrimeOperatorHom_substitution q e _ 1 _ hU f x

omit D in
theorem activeBlock_inverse_substitution (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) (x : Place × Fin 3 → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeChart q e).symm
      ((ActiveBlockMatrices.Local.activeBlockGL e μ g)⁻¹.val *ᵥ RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeProjection q e x, RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q x) =
    (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ).symm
      ((g⁻¹).val *ᵥ RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x, (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2) := by
  rw [← map_inv]
  change RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeInclusion q (fun i =>
      (ActiveBlockMatrices.Local.activeBlockMatrix e μ g⁻¹ *ᵥ RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeProjection q e x) (e i)) +
      (RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q x).val = _
  rw [RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway_val, RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart_symm]
  funext i
  have hproj (τ : Place) (j : Fin 3) :
      RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeProjection q e x (e (τ, j)) = RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q (x (τ, j)) := by
    change RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q (x (e.symm (e (τ, j)))) = _
    rw [Equiv.symm_apply_apply]
  change RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicInclusion q
      ((ActiveBlockMatrices.Local.activeBlockMatrix e μ g⁻¹ *ᵥ RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeProjection q e x) (e i)) +
      (x i - RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicInclusion q (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q (x i))) =
    RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ ((g⁻¹).val *ᵥ RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) i +
      (x i - RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q μ (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) i)
  rw [ActiveBlockMatrices.Local.activeBlockMatrix_mulVec]
  simp only [hproj, RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion_apply, RepresentationTheory.Hecke.RadialDilation.CanonicalVacuumTensor.Realization.finiteBlockProjection_apply]
  rcases i with ⟨τ, i⟩
  by_cases hi : τ = μ
  · subst τ
    simp only [↓reduceIte]
    rfl
  · simp only [hi, ite_false, zero_add, sub_zero]
    abel

theorem activeFiniteLift_block_substitution (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3)) (x : Place × Fin 3 → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (D.finite.action (activeFiniteLift q e μ D g) f).val x =
      f.val ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ).symm
        ((g⁻¹).val *ᵥ RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x, (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2)) := by
  rw [activeFiniteLift_full_substitution, activeBlock_inverse_substitution]

theorem activeFiniteLift_radial (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q)
    (x : Place × Fin 3 → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (D.finite.action (activeFiniteLift q e μ D g) (RepresentationTheory.Hecke.RadialDilation.Canonical.Realization.canonicalFiniteRadialEmbedding q μ b)).val x =
      b.val ((g⁻¹).val *ᵥ RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockProjection q μ x) *
        (RepresentationTheory.Hecke.RadialDilation.Canonical.Realization.finiteAwayVacuum q μ).val (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ x).2 := by
  rw [activeFiniteLift_block_substitution]
  change b.val ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ).symm _)).1) *
    (RepresentationTheory.Hecke.RadialDilation.Canonical.Realization.finiteAwayVacuum q μ).val ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ ((RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q μ).symm _)).2) = _
  rw [Homeomorph.apply_symm_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveLocalLift

import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveLocalLift

/-! # Block Family Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyLift.Local

noncomputable section

/-! Lift the full determinant-one local block family into the actual
finite Weil representation. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime] {Place : Type} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (e : (Place × Fin 3) ≃ Fin n)

local instance familyLocalMeasurable : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance familyLocalBorel : BorelSpace ℚ_[q] := ⟨rfl⟩

def blockFamilyMetaplectic (ψ : AddChar ℚ_[q] ℂ) :
    (Place → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) →* RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ where
  toFun g := RepresentationTheory.Weil.Local.SpecialLinearCommutators.Construction.specialLinearMetaplectic (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) ψ
    (BlockFamilyMatrices.Local.blockFamilyGL e g) (BlockFamilyMatrices.Local.blockFamilyMatrix_det e g)
  map_one' := by
    apply Subtype.ext
    change RepresentationTheory.Weil.Local.LinearIntertwiner.Construction.linearOscillator ψ (BlockFamilyMatrices.Local.blockFamilyGL e 1) = 1
    rw [map_one]
    exact RepresentationTheory.Weil.Local.LinearOscillatorHom.Construction.linearOscillator_one n ψ
  map_mul' g h := by
    apply Subtype.ext
    change RepresentationTheory.Weil.Local.LinearIntertwiner.Construction.linearOscillator ψ (BlockFamilyMatrices.Local.blockFamilyGL e (g * h)) =
      RepresentationTheory.Weil.Local.LinearIntertwiner.Construction.linearOscillator ψ (BlockFamilyMatrices.Local.blockFamilyGL e g) * RepresentationTheory.Weil.Local.LinearIntertwiner.Construction.linearOscillator ψ (BlockFamilyMatrices.Local.blockFamilyGL e h)
    rw [map_mul, RepresentationTheory.Weil.Local.LinearOscillatorHom.Construction.linearOscillator_mul]

variable {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)

def blockFamilyFiniteLift : (Place → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) →* MpF :=
  (RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift q e D).comp
    (blockFamilyMetaplectic q e (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D))

theorem blockFamilyFiniteLift_projection (g : Place → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    D.finite.project (blockFamilyFiniteLift q e D g) =
      RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q e (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic (BlockFamilyMatrices.Local.blockFamilyGL e g)) :=
  (RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift_spec q e D _).1

theorem blockFamilyFiniteLift_dual_projection (g : Place → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom
      (D.finite.project (blockFamilyFiniteLift q e D (fun τ => Contragredient.Local.contragredient ℚ_[q] (g τ)))) =
        BlockFamilyMatrices.Local.blockFamilySymplectic e g := by
  rw [blockFamilyFiniteLift_projection]
  exact RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion_projection q _

theorem blockFamilyFiniteLift_substitution (g : Place → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3)) (x : Place × Fin 3 → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (D.finite.action (blockFamilyFiniteLift q e D g) f).val x =
      f.val ((RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeChart q e).symm
        ((BlockFamilyMatrices.Local.blockFamilyGL e g)⁻¹.val *ᵥ RepresentationTheory.Hecke.RadialDilation.IndexedPrimeChart.Realization.indexedPrimeProjection q e x, RepresentationTheory.Hecke.RadialDilation.PrimeChart.Realization.fullPrimeAway q x)) := by
  change (D.finite.action (RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift q e D
    (blockFamilyMetaplectic q e (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D) g)) f).val x = _
  rw [(RepresentationTheory.Hecke.RadialDilation.IndexedPrimeBareLift.Realization.indexedPrimeMetaplecticLift_spec q e D
    (blockFamilyMetaplectic q e (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D) g)).2]
  have hU : ∀ f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n, ∀ y,
      (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D)
        (blockFamilyMetaplectic q e (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D) g) f).val y =
        (1 : ℂ) * f.val ((BlockFamilyMatrices.Local.blockFamilyGL e g)⁻¹.val *ᵥ y) := by
    intro f y
    rw [one_mul]
    exact RepresentationTheory.Weil.Local.SpecialLinearCommutators.Construction.specialLinearMetaplectic_apply (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete q) (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finiteLocalCharacter q D)
      (BlockFamilyMatrices.Local.blockFamilyGL e g) (BlockFamilyMatrices.Local.blockFamilyMatrix_det e g) f y
  simpa only [one_mul] using RepresentationTheory.Hecke.RadialDilation.IndexedPrimeSubstitution.Realization.indexedPrimeOperatorHom_substitution q e _ 1 _ hU f x

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyLift.Local

import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TracePairing
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierHeisenberg

/-! # Trace Heisenberg -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TraceHeisenberg.CM

noncomputable section

/-! The actual Heisenberg operators agree exactly in number-field
positions and rational trace-dual coordinates. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTestCoordinates.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TracePairing.CM

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem position_sub (x q : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    TracePairing.CM.position F N (fun i => x i - q i) = fun i => TracePairing.CM.position F N x i - TracePairing.CM.position F N q i :=
  (TracePairing.CM.position F N).map_sub x q

theorem position_half_sub (x q : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    TracePairing.CM.position F N (fun i => x i - algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (1 / 2) * q i) =
      fun i => TracePairing.CM.position F N x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * TracePairing.CM.position F N q i := by
  have hs : (fun i => x i - algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (1 / 2) * q i) =
      x - (1 / 2 : ℚ) • q := by
    funext i
    simp only [Pi.sub_apply, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
  rw [hs, map_sub, map_smul]
  funext i
  simp only [Pi.sub_apply, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]

theorem phase_trace (p q x : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    (∑ i, TracePairing.CM.momentum F N p i * (TracePairing.CM.position F N x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * TracePairing.CM.position F N q i)) =
      AdelicTrace.CM.trace F
        (∑ j, p j * (x j - algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (1 / 2) * q j)) := by
  have h := TracePairing.CM.pairing F N (fun i => x i - algebraMap ℚ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (1 / 2) * q i) p
  rw [position_half_sub] at h
  have hl : (∑ i, TracePairing.CM.momentum F N p i *
      (TracePairing.CM.position F N x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * TracePairing.CM.position F N q i)) =
      ∑ i, (TracePairing.CM.position F N x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * TracePairing.CM.position F N q i) * TracePairing.CM.momentum F N p i :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  refine hl.trans (h.trans ?_)
  apply congrArg (AdelicTrace.CM.trace F)
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem heisenberg_trace (p q x : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
    (φ : (Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) → ℂ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character (TracePairing.CM.momentum F N p) (TracePairing.CM.position F N q)
        (φ ∘ (TracePairing.CM.position F N).symm) (TracePairing.CM.position F N x) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg (HeckeCycles.NumberField.FiniteCharacter.CM.character F) p q φ x := by
  unfold RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg
  rw [phase_trace, AdelicTrace.CM.character_trace]
  congr 1
  change φ ((TracePairing.CM.position F N).symm (fun i => TracePairing.CM.position F N x i - TracePairing.CM.position F N q i)) = _
  rw [← position_sub, ContinuousLinearEquiv.symm_apply_apply]

def operator (p q : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N ≃ₗ[ℂ] RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N :=
  (AdelicTestCoordinates.CM.equivalence F N).symm.trans
    ((FourierHeisenberg.CM.equivalence (TracePairing.CM.momentum F N p) (TracePairing.CM.position F N q)).trans
      (AdelicTestCoordinates.CM.equivalence F N))

theorem operator_apply (p q : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
    (φ : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N) (x : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    (operator F N p q φ).val x =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg (HeckeCycles.NumberField.FiniteCharacter.CM.character F) p q φ.val x :=
  heisenberg_trace F N p q x φ.val

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TraceHeisenberg.CM

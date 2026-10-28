import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TracePhase
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TraceHeisenberg
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ReindexHeisenberg

/-! # Trace Test Heisenberg -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TraceTestHeisenberg.CM

noncomputable section

/-! Exact Heisenberg comparison after trace coordinates and arbitrary
relabeling of the rational position index. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTestCoordinates.CM

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
  {I : Type*} [Fintype I] (e : I ≃ Finite.AdelicTestCoordinates.CM.Index F N)

def tests : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N :=
  (Finite.ReindexHeisenberg.CM.Pairing.testEquiv e).trans (Finite.AdelicTestCoordinates.CM.equivalence F N)

def phases : ((Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ≃ₜ ((I ⊕ I) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :=
  (Finite.TracePhase.CM.coordinates F N).toHomeomorph.trans
    (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex (e.symm.sumCongr e.symm))

omit [Fintype I] in
theorem momentum (z : (Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e (fun i => phases F N e z (.inl i)) =
      Finite.TracePairing.CM.momentum F N (fun i => z (.inr i)) := by
  funext i
  change Finite.TracePhase.CM.coordinates F N z (.inl (e (e.symm i))) = _
  rw [Equiv.apply_symm_apply, Finite.TracePhase.CM.coordinates_left]

omit [Fintype I] in
theorem position (z : (Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e (fun i => phases F N e z (.inr i)) =
      Finite.TracePairing.CM.position F N (fun i => z (.inl i)) := by
  funext i
  change Finite.TracePhase.CM.coordinates F N z (.inr (e (e.symm i))) = _
  rw [Equiv.apply_symm_apply, Finite.TracePhase.CM.coordinates_right]

theorem intertwines (z : (Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    tests F N e (Finite.FourierHeisenberg.CM.operator
      (fun i => phases F N e z (.inl i)) (fun i => phases F N e z (.inr i)) φ) =
      Finite.TraceHeisenberg.CM.operator F N (fun i => z (.inr i)) (fun i => z (.inl i))
        (tests F N e φ) := by
  change Finite.AdelicTestCoordinates.CM.equivalence F N (Finite.ReindexHeisenberg.CM.Pairing.testEquiv e
    (Finite.FourierHeisenberg.CM.operator _ _ φ)) = _
  rw [Finite.ReindexHeisenberg.CM.heisenberg_reindex, momentum, position]
  change Finite.AdelicTestCoordinates.CM.equivalence F N (Finite.FourierHeisenberg.CM.operator _ _
      (Finite.ReindexHeisenberg.CM.Pairing.testEquiv e φ)) =
    Finite.AdelicTestCoordinates.CM.equivalence F N (Finite.FourierHeisenberg.CM.operator _ _
      ((Finite.AdelicTestCoordinates.CM.equivalence F N).symm (Finite.AdelicTestCoordinates.CM.equivalence F N (Finite.ReindexHeisenberg.CM.Pairing.testEquiv e φ))))
  rw [LinearEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TraceTestHeisenberg.CM

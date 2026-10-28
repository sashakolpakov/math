import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtaleWittModule
import OAI.NumberTheory.PadicHodge.PeriodInvariants.WittFiniteUnramified
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Smooth.Fiber

/-! # Finite Etale Witt Lift -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtaleWittLift

noncomputable section

/-! # Actual Witt vectors lift finite free etale algebras over perfect domains -/

attribute [local instance] WittAlgebraFunctor.wittAlgebra

universe u
variable (p : ℕ) [Fact p.Prime] (R S : Type u) [CommRing R] [IsDomain R] [CommRing S]
  [Nontrivial S] [Algebra R S] [CharP R p] [PerfectRing R p]
  [Module.Free R S] [Module.Finite R S] [Algebra.Etale R S]

theorem etale : Algebra.Etale (WittVector p R) (WittVector p S) := by
  let := FiniteEtaleWittModule.targetCharP p R S
  let := FiniteEtaleWittModule.targetPerfect p R S
  have := FiniteEtaleWittModule.free p R S
  have := FiniteEtaleWittModule.finite p R S
  have : Module.FinitePresentation (WittVector p R) (WittVector p S) :=
    Module.finitePresentation_of_projective _ _
  have : Algebra.FinitePresentation (WittVector p R) (WittVector p S) :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite (R := WittVector p R)
      (S := WittVector p S)).mp inferInstance
  have := WittFiniteUnramified.unramified p R S
  exact Algebra.Etale.of_formallyUnramified_of_flat

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtaleWittLift

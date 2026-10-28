import OAI.NumberTheory.PadicHodge.PeriodInvariants.WittFiniteBasis
import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtalePerfectAlgebra

/-! # Finite Etale Witt Module -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtaleWittModule

noncomputable section

/-! # Witt vectors preserve finite free modules of finite etale algebras over perfect domains -/

attribute [local instance] WittAlgebraFunctor.wittAlgebra

universe u
variable (p : ℕ) [Fact p.Prime] (R S : Type u) [CommRing R] [IsDomain R] [CommRing S]
  [Nontrivial S] [Algebra R S] [CharP R p] [PerfectRing R p]
  [Module.Free R S] [Module.Finite R S] [Algebra.Etale R S]

abbrev targetCharP : CharP S p :=
  CharP.of_ringHom_of_ne_zero (algebraMap R S) p (Fact.out : p.Prime).ne_zero

abbrev targetPerfect : PerfectRing S p := by
  let := targetCharP p R S
  exact FiniteEtalePerfectAlgebra.perfectRing p R S

def basis : Module.Basis (Module.Free.ChooseBasisIndex R S) (WittVector p R) (WittVector p S) := by
  classical
  let := targetCharP p R S
  let := targetPerfect p R S
  let : Fintype (Module.Free.ChooseBasisIndex R S) := Fintype.ofFinite _
  exact WittFiniteBasis.basis p (Module.Free.chooseBasis R S)

theorem free : Module.Free (WittVector p R) (WittVector p S) := Module.Free.of_basis (basis p R S)

theorem finite : Module.Finite (WittVector p R) (WittVector p S) := Module.Finite.of_basis (basis p R S)

theorem flat : Module.Flat (WittVector p R) (WittVector p S) := by
  have := free p R S
  infer_instance

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtaleWittModule

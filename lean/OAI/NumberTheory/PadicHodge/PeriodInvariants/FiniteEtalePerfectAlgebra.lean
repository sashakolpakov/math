import OAI.NumberTheory.PadicHodge.PeriodInvariants.FrobeniusBasis
import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteFreeFiberSurjectivity
import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtalePerfectField
import OAI.NumberTheory.PadicHodge.PeriodInvariants.PerfectQuotient
import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleDomainReduced
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Finite Etale Perfect Algebra -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtalePerfectAlgebra

noncomputable section

/-! # Finite free étale algebras over a perfect domain are perfect

The target may be disconnected. Its reducedness is derived from étaleness.
-/

open scoped TensorProduct

universe u
variable (p : ℕ) [Fact p.Prime] (R S : Type u) [CommRing R] [IsDomain R]
  [CommRing S] [Nontrivial S] [Algebra R S] [CharP R p] [CharP S p] [PerfectRing R p]
  [Module.Free R S] [Module.Finite R S] [Algebra.Etale R S]

include R in
theorem perfectRing : PerfectRing S p := by
  classical
  have : IsReduced S := EtaleDomainReduced.reduced R S
  let ι := Module.Free.ChooseBasisIndex R S
  let : Fintype ι := Fintype.ofFinite ι
  let b : Module.Basis ι R S := Module.Free.chooseBasis R S
  apply PerfectRing.ofSurjective S p
  apply FrobeniusBasis.frobenius_surjective p b
  apply (FiniteFreeFiberSurjectivity.bijective (FrobeniusBasis.linear p b) ?_).surjective
  intro m hm
  let F := R ⧸ m
  let : Field F := Ideal.Quotient.field m
  have : CharP F p := CharP.of_ringHom_of_ne_zero (Ideal.Quotient.mk m) p (Fact.out : p.Prime).ne_zero
  have : PerfectRing F p := PerfectQuotient.perfectRing p R m
  have : CharP (F ⊗[R] S) p := CharP.of_ringHom_of_ne_zero
    (algebraMap F (F ⊗[R] S)) p (Fact.out : p.Prime).ne_zero
  have : PerfectRing (F ⊗[R] S) p := FiniteEtalePerfectField.perfectRing p F (F ⊗[R] S)
  rw [FrobeniusBasis.baseChange]
  exact FrobeniusBasis.surjective_of_perfect p (b.baseChange F)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtalePerfectAlgebra

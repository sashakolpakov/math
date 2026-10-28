import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.BaseChangeNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.AlgebraEquivalence
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Products
import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtaleWittModule
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Witt Splitting -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.WittSplitting

noncomputable section

/-! Actual finite étale Witt algebras split into copies of W(k̄) after canonical base change. -/

open scoped TensorProduct

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

universe u

variable (p : ℕ) [Fact p.Prime] (k A : Type u) [Field k] [CommRing A] [Algebra k A]
  [CharP k p] [PerfectRing k p] [Nontrivial A] [Module.Finite k A] [Algebra.Etale k A]

local notation "Ω" => AlgebraicClosure k
local notation "T" => Ω ⊗[k] A

omit p [Fact p.Prime] [CharP k p] [PerfectRing k p] [Nontrivial A] [Algebra.Etale k A] in
theorem finite_index : Finite (PrimeSpectrum T) := by
  let : IsArtinianRing T := IsArtinianRing.of_finite Ω T
  infer_instance

def equiv : (WittVector p Ω) ⊗[WittVector p k] (WittVector p A) ≃ₐ[WittVector p Ω]
    (PrimeSpectrum T → WittVector p Ω) := by
  let := PeriodInvariants.FiniteEtaleWittModule.targetCharP p k A
  let := PeriodInvariants.FiniteEtaleWittModule.targetPerfect p k A
  let := PeriodInvariants.FiniteEtaleWittModule.targetCharP p Ω T
  let := PeriodInvariants.FiniteEtaleWittModule.targetPerfect p Ω T
  let : Fintype (Module.Free.ChooseBasisIndex k A) := Fintype.ofFinite _
  exact (Witt.BaseChangeNaturality.Finite.equiv p k Ω A (Module.Free.chooseBasis k A)).trans
    ((Witt.AlgebraEquivalence.map p Ω (Algebra.FormallyEtale.equivPiOfIsSepClosed Ω T)).trans
      (Witt.Products.algebraEquiv p (fun _ : PrimeSpectrum T => Ω) Ω))

theorem coeff (z : (WittVector p Ω) ⊗[WittVector p k] (WittVector p A)) (i : PrimeSpectrum T) (n : ℕ) :
    (equiv p k A z i).coeff n =
      Algebra.FormallyEtale.equivPiOfIsSepClosed Ω T ((Witt.BaseChangeNaturality.Finite.map p k Ω A z).coeff n) i := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.WittSplitting

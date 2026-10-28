import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtaleIntegralTrace
import Mathlib.FieldTheory.Perfect

/-! # Finite Etale Perfect Field -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtalePerfectField

noncomputable section

/-! # Finite étale algebras over a perfect field are perfect rings -/

universe u
variable (p : ℕ) [Fact p.Prime] (K E : Type u) [Field K] [CommRing E]
  [CharP K p] [PerfectRing K p] [Algebra K E] [Algebra.Etale K E]

include K in
theorem perfectRing : PerfectRing E p := by
  classical
  have : PerfectField K := PerfectRing.toPerfectField K p
  obtain ⟨ι, _, L, hL, hKL, e, hfin⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K E).mp inferInstance
  let : ∀ i, Field (L i) := hL
  let : ∀ i, Algebra K (L i) := hKL
  have : ∀ i, Module.Finite K (L i) := fun i => (hfin i).1
  have : ∀ i, CharP (L i) p := fun i => charP_of_injective_algebraMap (algebraMap K (L i)).injective p
  have : ∀ i, PerfectField (L i) := fun i => Algebra.IsAlgebraic.perfectField K
  have : ∀ i, PerfectRing (L i) p := fun i => PerfectField.toPerfectRing p
  constructor
  constructor
  · intro x y h
    apply e.injective
    funext i
    apply (frobeniusEquiv (L i) p).injective
    simpa only [map_pow, Pi.pow_apply, frobeniusEquiv_def] using congrFun (congrArg e h) i
  · intro x
    refine ⟨e.symm (fun i => (frobeniusEquiv (L i) p).symm (e x i)), ?_⟩
    apply e.injective
    ext i
    simp only [map_pow, AlgEquiv.apply_symm_apply, Pi.pow_apply, frobeniusEquiv_symm_pow_p]

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtalePerfectField

import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.Modules
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.WittFinite
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTorsion

/-! # Witt Cohomology Finite -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.WittCohomologyFinite

noncomputable section

/-!
# IntegralComparison: finite generation of actual bounded Witt cohomology gives finite groups
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of (WittVector p k)))

local notation "W" => WittVector p k
local notation "CoeffW" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "WittIdeal" => Ideal.span {(p : W)}
local notation "wittDP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k

def coefficientTruncate (n : ℕ) : CoeffW →+* TruncatedWittVector p (n + 1) k :=
  (WittVector.truncate (p := p) (R := k) (n + 1)).comp ULift.ringEquiv.toRingHom

omit [Fintype k] [CharP k p] in
theorem coefficientTruncate_surjective (n : ℕ) : Function.Surjective (coefficientTruncate p k n) :=
  (WittVector.truncate_surjective (p := p) (n := n + 1) (R := k)).comp ULift.ringEquiv.surjective

theorem kernel_smul_zero (n i : ℕ) (r : CoeffW) (hr : coefficientTruncate p k n r = 0)
    (x : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := WittIdeal) (δ := wittDP) f n i) : r • x = 0 := by
  have hw : r.down ∈ WittIdeal ^ (n + 1) := by
    rw [Truncated.WittFinite.powerIdeal_eq_kernel p k n]
    exact hr
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hw
  obtain ⟨a, ha⟩ := hw
  have he : r = (p : CoeffW) ^ (n + 1) * ULift.up a := by
    apply ULift.ext
    exact ha
  rw [he, mul_smul]
  exact CohomologyTorsion.cohomology_smul_zero f n i _

theorem finite (n i : ℕ)
    [Module.Finite CoeffW (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := WittIdeal) (δ := wittDP) f n i)] :
    Finite (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := WittIdeal) (δ := wittDP) f n i) := by
  let : Finite (TruncatedWittVector p (n + 1) k) := inferInstanceAs (Finite (Fin (n + 1) → k))
  exact FiniteCoefficient.Modules.finite CoeffW (TruncatedWittVector p (n + 1) k) _
    (coefficientTruncate p k n) (coefficientTruncate_surjective p k n) (kernel_smul_zero p k f n i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.WittCohomologyFinite

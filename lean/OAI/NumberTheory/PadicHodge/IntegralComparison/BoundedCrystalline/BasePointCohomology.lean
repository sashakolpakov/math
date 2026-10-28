import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BasePointFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalFramePoint
import OAI.NumberTheory.PadicHodge.IntegralComparison.TerminalModuleProjective
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafLinearSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.WittFinite
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTorsion

/-! # Base Point Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.BasePointCohomology

noncomputable section

/-! Cohomology of the base field on the actual bounded crystalline site. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BasePointFrame

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p] (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Crystalline.BasePointFrame.baseMap p k) n
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Crystalline.BasePointFrame.baseMap p k) n

instance ring_nontrivial : Nontrivial (Crystalline.BasePointFrame.object p k n).ring :=
  Function.Surjective.nontrivial (Truncated.Witt.reduction_surjective p k n)

instance ring_local : IsLocalRing (Crystalline.BasePointFrame.object p k n).ring :=
  IsLocalRing.of_surjective' (Truncated.Witt.quotient p k n) Ideal.Quotient.mk_surjective

theorem covering_eq_top (S : Sieve (Crystalline.BasePointFrame.bounded p k n)) (hS : S ∈ T (Crystalline.BasePointFrame.bounded p k n)) : S = ⊤ :=
  RepresentablePointTopology.covering_eq_top (Crystalline.BasePointFrame.bounded p k n) T
    (RepresentablePointTopology.restricted_le (Crystalline.BasePointFrame.bounded p k n)
      (Site.inclusion (Crystalline.BasePointFrame.baseMap p k) n) BigCrystallineSite.Object.topology
        (Crystalline.LocalFramePoint.topology_le (Crystalline.BasePointFrame.object p k n))) S hS

instance unit_projective : Projective (CrystallineCohomology.constantUnit
    (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Crystalline.BasePointFrame.baseMap p k) n) :=
  TerminalModuleProjective.projective T R (covering_eq_top p k n) (Crystalline.BasePointFrame.isTerminal p k n)

theorem eq_zero (i : ℕ) (z : H (i + 1)) : z = 0 :=
  Abelian.Ext.eq_zero_of_projective z

instance subsingleton (i : ℕ) : Subsingleton (H (i + 1)) :=
  subsingleton_of_forall_eq 0 (eq_zero p k n i)

def degreeZero : H 0 ≃ₗ[R]
    (BigCrystallineCohomology.largePresheaf (Crystalline.BasePointFrame.baseMap p k)).obj (op (Crystalline.BasePointFrame.object p k n)) :=
  (Module.SheafLinearSections.degreeZeroLinearEquiv T R (Crystalline.BasePointFrame.isTerminal p k n)
    (CrystallineCohomology.structureSheaf (Crystalline.BasePointFrame.baseMap p k) n)).trans
      (((Bounded.CohomologyTorsion.structurePresheafIso (Crystalline.BasePointFrame.baseMap p k) n).app
        (op (Crystalline.BasePointFrame.bounded p k n))).symm.toLinearEquiv)

instance finite (i : ℕ) : Finite (H i) := by
  cases i with
  | zero =>
      let : Finite (Truncated.Witt.Ring p k n) := Truncated.WittFinite.finite p k n
      let : Finite ((BigCrystallineCohomology.largePresheaf (Crystalline.BasePointFrame.baseMap p k)).obj
          (op (Crystalline.BasePointFrame.object p k n))) :=
        inferInstanceAs (Finite (ULift.{u + 1} (Truncated.Witt.Ring p k n)))
      exact Finite.of_injective _ (degreeZero p k n).injective
  | succ i => infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.BasePointCohomology

import OAI.AlgebraicGeometry.Divisors.LineBundles.IsomorphismDivisorPushforward
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Fiber Pushforward -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.FiberPushforward.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual residue-weighted pushforward restricted to a closed fiber
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y W Z : Scheme.{0}}
    (i : X ⟶ Y) (j : Z ⟶ Y) (k : W ⟶ X) (q : W ⟶ Z)
    [IsClosedImmersion j] [IsClosedImmersion k]
    (hcomm : k ≫ i = q ≫ j)

include hcomm in
theorem closedSquare_residueDegree (w : W) : i.residueDegree (k w) = q.residueDegree w := by
  have hc := congrArg (fun f : W ⟶ Y => f.residueDegree w) hcomm
  simpa only [IntersectionTheory.ProjectionFormula.CyclePushforward.residueDegree_comp, IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle.residueDegree_immersion,
    one_mul, mul_one] using hc

include hcomm in
theorem closedSquare_pointPushforward
    (hcover : Set.range k = i ⁻¹' Set.range j) (z : X →₀ ℚ) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward q (Finsupp.comapDomain k z k.isClosedEmbedding.injective.injOn) =
      Finsupp.comapDomain j (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i z) j.isClosedEmbedding.injective.injOn := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw =>
    rw [Finsupp.comapDomain_add_of_injective k.isClosedEmbedding.injective, map_add,
      map_add, Finsupp.comapDomain_add_of_injective j.isClosedEmbedding.injective, hz, hw]
  | single x a =>
    by_cases hx : x ∈ Set.range k
    · obtain ⟨w, rfl⟩ := hx
      have hc : i (k w) = j (q w) := congrArg (fun f : W ⟶ Y => f w) hcomm
      rw [Finsupp.comapDomain_single, IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single, IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single,
        hc, Finsupp.comapDomain_single, closedSquare_residueDegree i j k q hcomm]
    · have hix : i x ∉ Set.range j := by
        intro h
        apply hx
        rw [hcover]
        exact h
      rw [Finsupp.comapDomain_single_of_not_mem_range hx, map_zero,
        IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single, Finsupp.comapDomain_single_of_not_mem_range hix]

theorem pullbackClosed_pointPushforward (i : X ⟶ Y) (j : Z ⟶ Y) [IsClosedImmersion j]
    (z : X →₀ ℚ) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (pullback.snd i j)
      (Finsupp.comapDomain (pullback.fst i j) z (pullback.fst i j).isClosedEmbedding.injective.injOn) =
        Finsupp.comapDomain j (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i z) j.isClosedEmbedding.injective.injOn :=
  closedSquare_pointPushforward i j (pullback.fst i j) (pullback.snd i j)
    pullback.condition (Scheme.Pullback.range_fst i j) z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.FiberPushforward.BundleCycles

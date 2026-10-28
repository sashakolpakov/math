import OAI.AlgebraicGeometry.Divisors.LineBundles.IsomorphismDivisorPushforward
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Fiber Pushforward -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.FiberPushforward.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual residue-weighted point pushforward commutes with open base change -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y W Z : Scheme.{0}}
    (f : X ⟶ Y) (j : Z ⟶ Y) (k : W ⟶ X) (q : W ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion k] (hcomm : k ≫ f = q ≫ j)

include hcomm in
theorem openSquare_residueDegree (w : W) : f.residueDegree (k w) = q.residueDegree w := by
  have h := congrArg (fun f : W ⟶ Y => f.residueDegree w) hcomm
  simpa only [IntersectionTheory.ProjectionFormula.CyclePushforward.residueDegree_comp, IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle.residueDegree_immersion, one_mul, mul_one] using h

include hcomm in
theorem openSquare_pointPushforward (hcover : Set.range k = f ⁻¹' Set.range j) (z : X →₀ ℚ) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward q (Finsupp.comapDomain k z k.isOpenEmbedding.injective.injOn) =
      Finsupp.comapDomain j (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f z) j.isOpenEmbedding.injective.injOn := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw =>
    rw [Finsupp.comapDomain_add_of_injective k.isOpenEmbedding.injective, map_add,
      map_add, Finsupp.comapDomain_add_of_injective j.isOpenEmbedding.injective, hz, hw]
  | single x a =>
    by_cases hx : x ∈ Set.range k
    · obtain ⟨w, rfl⟩ := hx
      have hc : f (k w) = j (q w) := congrArg (fun f : W ⟶ Y => f w) hcomm
      rw [Finsupp.comapDomain_single, IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single, IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single,
        hc, Finsupp.comapDomain_single, openSquare_residueDegree f j k q hcomm]
    · have hfx : f x ∉ Set.range j := by
        intro h
        apply hx
        rw [hcover]
        exact h
      rw [Finsupp.comapDomain_single_of_not_mem_range hx, map_zero,
        IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single, Finsupp.comapDomain_single_of_not_mem_range hfx]

theorem morphismRestrict_pointPushforward {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (z : X →₀ ℚ) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (f ∣_ U)
      (Finsupp.comapDomain (f ⁻¹ᵁ U).ι z (f ⁻¹ᵁ U).ι.isOpenEmbedding.injective.injOn) =
        Finsupp.comapDomain U.ι (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f z) U.ι.isOpenEmbedding.injective.injOn := by
  apply openSquare_pointPushforward f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U) (morphismRestrict_ι f U).symm
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.FiberPushforward.BundleCycles

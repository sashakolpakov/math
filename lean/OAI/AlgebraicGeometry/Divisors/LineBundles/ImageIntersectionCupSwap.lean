import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport

/-! # Image Intersection Cup Swap -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ImageIntersectionCupSwap.BundleCycles

noncomputable section

/-! Even supported image-intersection cups commute with the literal support and degree identifications. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.ProjectionRightCup OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions

theorem imageIntersectionCup_swap {M P N : Type} [TopologicalSpace N]
    (u : M → N) (v : P → N) (hu : IsOpen (Set.range u)ᶜ) (hv : IsOpen (Set.range v)ᶜ) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range v)ᶜ (2 * q)) :
    CycleClass.Thom.Supported.Transport.Constructions.Class.supportDegreeTransport (TopCat.of N) (congrArg Set.compl (Set.inter_comm (Set.range u) (Set.range v)))
      (congrArg (fun n => 2 * n) (Nat.add_comm p q))
      (CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup u v hu hv p q a b) = CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup v u hv hu q p b a := by
  have hs := (CycleClass.Thom.Supported.Transport.Constructions.Class.cupSwapTransport_eq_transport (TopCat.of N) (Set.range v)ᶜ (Set.range u)ᶜ (2 * q) (2 * p)
    (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of N) (Set.range u)ᶜ (Set.range v)ᶜ hu hv (2 * p) (2 * q) a b)).symm.trans
      (CycleClass.Thom.Supported.Transport.Constructions.ProjectionRightCup.evenCup_swap (TopCat.of N) (Set.range v)ᶜ (Set.range u)ᶜ hv hu q (2 * p) b a)
  have h := congrArg (CycleClass.Thom.Supported.Transport.Constructions.Class.supportDegreeTransport (TopCat.of N)
    (CycleClass.Thom.ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq v u) (Nat.mul_add 2 q p).symm) hs
  rw [CycleClass.Thom.Supported.Transport.Constructions.Class.supportDegreeTransport_trans] at h
  rw [CycleClass.Thom.Supported.Transport.Constructions.Class.imageIntersectionCup_eq_transport, CycleClass.Thom.Supported.Transport.Constructions.Class.imageIntersectionCup_eq_transport]
  exact (CycleClass.Thom.Supported.Transport.Constructions.Class.supportDegreeTransport_trans (TopCat.of N)
    (CycleClass.Thom.ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq u v)
    (congrArg Set.compl (Set.inter_comm (Set.range u) (Set.range v)))
    (Nat.mul_add 2 p q).symm (congrArg (fun n => 2 * n) (Nat.add_comm p q))
    (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of N) (Set.range u)ᶜ (Set.range v)ᶜ hu hv (2 * p) (2 * q) a b)).trans h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ImageIntersectionCupSwap.BundleCycles

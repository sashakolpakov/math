import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactLeftCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupForget

/-! # Compact Thom Cup Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomCupSupport.Constructions

noncomputable section

/-! Cup by a supported class retains the literal intersection with every compact test support. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) [T2Space X] (C : Set X) (hC : IsOpen C)

def thomCompactIntersection (K : Compacts X) : Compacts X :=
  ⟨(K : Set X) ∩ Cᶜ, K.isCompact.inter_right hC.isClosed_compl⟩

theorem thomCompactIntersection_le (K : Compacts X) : thomCompactIntersection X C hC K ≤ K := by
  let _ := (inferInstance : T2Space X)
  exact Set.inter_subset_left

theorem thomCompactIntersection_complement (K : Compacts X) :
    C ∪ (K : Set X)ᶜ = (thomCompactIntersection X C hC K : Set X)ᶜ := by
  let _ := (inferInstance : T2Space X)
  ext x
  change (x ∈ C ∨ x ∉ (K : Set X)) ↔ ¬ (x ∈ (K : Set X) ∧ x ∉ C)
  tauto

def thomCompactIntersectionClass (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X C p) (K : Compacts X)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X
      (thomCompactIntersection X C hC K : Set X)ᶜ (p+q) :=
  (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr X (thomCompactIntersection_complement X C hC K) (p+q)).hom
    (SupportCup.Constructions.twoSupportCohomologyCup X C (K : Set X)ᶜ hC K.isCompact.isClosed.isOpen_compl p q a b)

theorem thomCompactIntersectionClass_forget (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X C p) (K : Compacts X)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ q) :
    AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) (thomCompactIntersection_le X C hC K) (p+q)
      (thomCompactIntersectionClass X C hC p q a K b) =
    CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup (R := ℚ) X (K : Set X)ᶜ p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X C p a) b := by
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap_source_congr X
      (thomCompactIntersection_complement X C hC K)
      (Set.subset_union_right : (K : Set X)ᶜ ⊆ C ∪ (K : Set X)ᶜ)
      (Set.compl_subset_compl.mpr (thomCompactIntersection_le X C hC K)) (p+q))
    (SupportCup.Constructions.twoSupportCohomologyCup X C (K : Set X)ᶜ hC K.isCompact.isClosed.isOpen_compl p q a b)
  exact hc.trans (SupportCupForget.Constructions.twoSupportCohomologyCup_forget_left X C (K : Set X)ᶜ
    hC K.isCompact.isClosed.isOpen_compl p q a b)

theorem compactThomCup_retains_intersection (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X C p) (K : Compacts X)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ q) :
    CompactLeftCup.Constructions.compactCohomologyLeftCup X p q (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X C p a)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K q b) =
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X (thomCompactIntersection X C hC K) (p+q)
      (thomCompactIntersectionClass X C hC p q a K b) := by
  have hι := ConcreteCategory.congr_hom (AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap_ι (ModuleCat.of ℚ ℚ)
    (thomCompactIntersection_le X C hC K) (p+q))
    (thomCompactIntersectionClass X C hC p q a K b)
  rw [ConcreteCategory.comp_apply, thomCompactIntersectionClass_forget] at hι
  exact (CompactLeftCup.Constructions.compactCohomologyLeftCup_stage X p q
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X C p a) K b).trans hι

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomCupSupport.Constructions

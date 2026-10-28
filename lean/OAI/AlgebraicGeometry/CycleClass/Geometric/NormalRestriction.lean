import OAI.AlgebraicGeometry.CycleClass.Geometric.ImmersionNormalRecenter
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections

/-! # Normal Restriction -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Normalization of global relative classes on actual normal charts

Restriction of a global relative class gives the same germ on every open
neighborhood of a point. A normal neighborhood computes that stalk, so
the checked compatibility of normal-class germs implies equality of the
actual restrictions. No global Thom class is assumed or imported.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleClass.Geometric.NormalRestriction.Cycles

variable {R : Type} [Ring R] (A : ModuleCat.{0} R) (X : TopCat.{0})

/-- The germ of an actual global relative class can be computed after
restriction to any actual open neighborhood of the point. -/
@[reassoc]
theorem relativeCohomologyOpenRestriction_germ
    (S : Set X) (U : Opens X) (x : X) (hx : x ∈ U) (n : ℕ) :
    RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction A X S U n ≫
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf A X S n).germ U x hx =
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso A X S n).inv ≫
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf A X S n).germ ⊤ x
          (show x ∈ (⊤ : Opens X) from trivial) := by
  rw [RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction_eq, Category.assoc,
    TopCat.Presheaf.germ_res]

/-- Computing the germ through two different open restrictions gives
literally the same map from the global relative cohomology group. -/
@[reassoc]
theorem relativeCohomologyOpenRestriction_germ_eq
    (S : Set X) (U V : Opens X) (x : X)
    (hxU : x ∈ U) (hxV : x ∈ V) (n : ℕ) :
    RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction A X S U n ≫
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf A X S n).germ U x hxU =
      RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction A X S V n ≫
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf A X S n).germ V x hxV := by
  rw [relativeCohomologyOpenRestriction_germ, relativeCohomologyOpenRestriction_germ]

end CycleClass.Geometric.NormalRestriction.Cycles

variable {M N E : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : M → N} {x : M} {p : ℕ}
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)

/-- The explicit-degree normal class is nonzero, including in normal
dimension zero. This uses the actual normal-coordinate isomorphism. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin_ne_zero : P.rationalClassFin ≠ 0 := by
  intro h
  rw [P.rationalClassFin_eq_normalPullback] at h
  apply CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass_ne_zero p
  apply (P.relativeCohomologyIso (2 * p)).toLinearEquiv.injective
  simpa only [CategoryTheory.Iso.toLinearEquiv_apply, ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeCohomologyIso_hom,
    map_zero] using h

/-- A global class with normalized restriction on one normal chart
is nonzero in the genuine global relative cohomology group. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeClass_ne_zero_of_normalization
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ (2 * p))
    (hb : CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ P.openNeighborhood (2 * p) b = P.rationalClassFin) :
    b ≠ 0 := by
  intro h
  apply P.rationalClassFin_ne_zero
  rw [← hb, h, map_zero]

variable [NormedSpace ℂ E]

/-- If a global relative class is normalized on one differentiable
normal chart, it is normalized on any differentiable normal chart whose
center lies in the first neighborhood. The centers may be different. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin_restriction_eq_on_overlap
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
    {y : M} (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f y)
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)))
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)))
    (hyP : f y ∈ P.neighborhood)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ (2 * p))
    (hb : CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ P.openNeighborhood (2 * p) b = P.rationalClassFin) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ Q.openNeighborhood (2 * p) b = Q.rationalClassFin := by
  apply (Q.relativeCohomologyGermIso (2 * p)).toLinearEquiv.injective
  change Q.relativeCohomologyGerm (2 * p)
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range f)ᶜ Q.openNeighborhood (2 * p) b) =
    Q.relativeCohomologyGerm (2 * p) Q.rationalClassFin
  have hg := ConcreteCategory.congr_hom
    (CycleClass.Geometric.NormalRestriction.Cycles.relativeCohomologyOpenRestriction_germ_eq (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ Q.openNeighborhood P.openNeighborhood (f y)
      Q.point_mem_neighborhood hyP (2 * p)) b
  have hc := congrArg
    (fun c : P.relativeCohomology (ModuleCat.of ℚ ℚ) (2 * p) =>
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range f)ᶜ
        (2 * p)).germ P.openNeighborhood (f y) hyP c) hb
  exact hg.trans (hc.trans
    (P.rationalClassFin_germ_eq_on_overlap Q hP hQ y hyP Q.point_mem_neighborhood))

/-- In particular, normalization on one genuine differentiable normal
chart at a point implies normalization on every such chart at that point. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClassFin_restriction_eq_of_charts
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
    (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x)
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)))
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ (2 * p))
    (hb : CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ P.openNeighborhood (2 * p) b = P.rationalClassFin) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range f)ᶜ Q.openNeighborhood (2 * p) b = Q.rationalClassFin :=
  P.rationalClassFin_restriction_eq_on_overlap Q hP hQ P.point_mem_neighborhood b hb

end

end OAI.AlgebraicGeometry

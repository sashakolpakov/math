import OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionHolomorphy
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HomeomorphCohomology
import OAI.AlgebraicGeometry.Comparison.Betti.ProductHolomorphicAcyclicity

/-! # Intersection Acyclicity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionAcyclicity.Dolbeault

noncomputable section

/-! Every nonempty standard chart intersection of genuine complex projective
space has acyclic native holomorphic function sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

local instance (n : ℕ) (s : Finset (Fin (n + 1))) :
    HasExt.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of (IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s))) :=
  HasExt.standard _

theorem projectiveIntersection_holomorphicScalarSheaf_ext_vanish (n : ℕ)
    (s : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ s) (q : ℕ) :
    Subsingleton (Abelian.Ext.{1}
      (ConstantSheafSections.standardConstantSheaf (TopCat.of (IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s)))
      (Holomorphic.ScalarSheaf.Dolbeault.holomorphicScalarSheaf (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticModel
        (IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s)) (q + 1)) := by
  have := ProductHolomorphicAcyclicity.Dolbeault.product_holomorphicScalarSheaf_ext_vanish (IntersectionDomains.Dolbeault.projectiveIntersectionPunctures s i) q
  let e := Holomorphic.HomeomorphCohomology.Dolbeault.holomorphicHomeomorphExtEquiv (IntersectionDomains.Dolbeault.projectiveSchemeIntersectionChart n s i hi)
    (IntersectionHolomorphy.Dolbeault.projectiveSchemeIntersectionChart_holomorphic n s i hi)
    (IntersectionHolomorphy.Dolbeault.projectiveSchemeIntersectionChart_symm_holomorphic n s i hi) (q + 1)
  exact e.injective.subsingleton

theorem projectiveIntersection_holomorphicFunctionSheaf_cohomology_vanish (n : ℕ)
    (s : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ s) (q : ℕ) :
    Subsingleton (Sheaf.H.{0}
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticModel
        (IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s)) (q + 1)) := by
  have := ProductHolomorphicAcyclicity.Dolbeault.product_holomorphicFunctionSheaf_cohomology_vanish (IntersectionDomains.Dolbeault.projectiveIntersectionPunctures s i) q
  let e := Holomorphic.HomeomorphCohomology.Dolbeault.holomorphicHomeomorphCohomologyEquiv (IntersectionDomains.Dolbeault.projectiveSchemeIntersectionChart n s i hi)
    (IntersectionHolomorphy.Dolbeault.projectiveSchemeIntersectionChart_holomorphic n s i hi)
    (IntersectionHolomorphy.Dolbeault.projectiveSchemeIntersectionChart_symm_holomorphic n s i hi) (q + 1)
  exact e.injective.subsingleton

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionAcyclicity.Dolbeault

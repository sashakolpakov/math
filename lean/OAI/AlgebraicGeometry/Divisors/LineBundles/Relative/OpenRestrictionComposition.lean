import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections

/-! # Open Restriction Composition -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.OpenRestrictionComposition.BundleCycles

noncomputable section

/-! Restricting a global relative class through nested analytic opens equals the direct restriction. -/

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections.Cycles

variable (X : TopCat.{0}) (A : Set X) (U V : Opens X) (hUV : U ≤ V) (n : ℕ)

theorem relativeOpenRestriction_nested
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n) :
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) X A n).map (homOfLE hUV).op
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) X A V n a) =
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) X A U n a := by
  let P := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) X A n
  let e := (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) X A n).inv
  let i : V ⟶ (⊤ : Opens X) := homOfLE le_top
  let j : U ⟶ V := homOfLE hUV
  have h1 := CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction_eq (ModuleCat.of ℚ ℚ) X A V n
  have h2 := CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction_eq (ModuleCat.of ℚ ℚ) X A U n
  have hc := (Category.assoc e (P.map i.op) (P.map j.op)).trans
    (congrArg (fun f => e ≫ f) (P.map_comp i.op j.op).symm)
  have h := (congrArg (fun f => f ≫ P.map j.op) h1).trans (hc.trans h2.symm)
  exact ConcreteCategory.congr_hom h a

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.OpenRestrictionComposition.BundleCycles

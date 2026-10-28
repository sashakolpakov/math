import OAI.AlgebraicGeometry.Comparison.Betti.DisjointDerivedHom
import OAI.AlgebraicGeometry.Comparison.Betti.CoefficientDerivedNaturality

/-! # Disjoint Hypercohomology Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.DisjointHypercohomologyNaturality

noncomputable section

/-! The actual inverse-image maps in the disjoint hypercohomology decomposition commute with coefficient inclusions. -/

open _root_.CategoryTheory

variable {M N : TopCat.{0}} (f : M ⟶ N)
  {K L : CochainComplex (ConstantSheafSections.ComplexSheaves N) ℤ} (u : K ⟶ L) (n : ℤ)

theorem inverseImageHypercohomologyMap_postcomp (a : DisjointDerivedHom.complexHypercohomology N K n) :
    DisjointDerivedHom.inverseImageHypercohomologyMap f L n (a ≫ (DerivedCategory.Q.map u)⟦n⟧') =
      DisjointDerivedHom.inverseImageHypercohomologyMap f K n a ≫
        (DerivedCategory.Q.map (((TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (.up ℤ)).map u))⟦n⟧' := by
  let F := TopologicalSheafPullback.sheafInverseImage f
  let S := shiftFunctor (DerivedCategory (ConstantSheafSections.ComplexSheaves M)) n
  have hn := F.mapDerivedCategoryFactors.hom.naturality u
  change F.mapDerivedCategory.map (DerivedCategory.Q.map u) ≫ F.mapDerivedCategoryFactors.hom.app L =
    F.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map u) at hn
  have hs := (S.map_comp (F.mapDerivedCategory.map (DerivedCategory.Q.map u))
    (F.mapDerivedCategoryFactors.hom.app L)).symm.trans
      ((congrArg S.map hn).trans (S.map_comp (F.mapDerivedCategoryFactors.hom.app K)
        (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map u))))
  change (Derived.ConstantPullback.derivedConstantPullbackIso f).inv ≫
      ShiftedHom.map (a ≫ (DerivedCategory.Q.map u)⟦n⟧') F.mapDerivedCategory ≫
        S.map (F.mapDerivedCategoryFactors.hom.app L) =
    ((Derived.ConstantPullback.derivedConstantPullbackIso f).inv ≫ ShiftedHom.map a F.mapDerivedCategory ≫
      S.map (F.mapDerivedCategoryFactors.hom.app K)) ≫
        S.map (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map u))
  rw [CoefficientDerivedNaturality.Ext.derivedShiftedHom_map_postcomp F u]
  simp only [Category.assoc]
  exact congrArg (fun t => (Derived.ConstantPullback.derivedConstantPullbackIso f).inv ≫
    ShiftedHom.map a F.mapDerivedCategory ≫ t) hs

end

end OAI.AlgebraicGeometry.Comparison.Betti.DisjointHypercohomologyNaturality

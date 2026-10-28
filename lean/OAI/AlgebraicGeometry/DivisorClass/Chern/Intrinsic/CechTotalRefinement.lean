import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.RefinementGlobal

/-! # Cech Total Refinement -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.CechTotalRefinement

noncomputable section

/-! Refinement of the native Cech bicomplex preserves both actual augmentation edges. -/

open _root_.CategoryTheory _root_.TopologicalSpace _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I J : Type} (U : I → Opens X) (V : J → Opens X)
  (r : J → I) (hr : ∀ j, V j ≤ U (r j))
  (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)

def nativeCechBicomplexRefinement : SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K ⟶ SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex V K :=
  CochainComplex.ofHom (fun q => Cech.AbelianRefinement.nativeCechRefinement U V r hr (K.X q).obj)
    (fun q => (Cech.AbelianRefinement.nativeCechRefinement_naturality U V r hr (K.d q (q + 1)).hom).symm)

def nativeCechTotalRefinement : (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K).total (.up ℕ) ⟶
    (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex V K).total (.up ℕ) :=
  HomologicalComplex₂.total.map (nativeCechBicomplexRefinement U V r hr K) (.up ℕ)

theorem nativeCechHorizontalEdge_refinement :
    FlasqueCechD.abelianCechHorizontalEdge U K ≫ nativeCechTotalRefinement U V r hr K =
      FlasqueCechD.abelianCechHorizontalEdge V K := by
  apply HomologicalComplex.Hom.ext
  funext q
  rw [HomologicalComplex.comp_f, FlasqueCechD.abelianCechHorizontalEdge_f, FlasqueCechD.abelianCechHorizontalEdge_f,
    Category.assoc, nativeCechTotalRefinement, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
  congr 1
  exact Cech.RefinementGlobal.nativeCechRefinement_global U V r hr (K.X q)

variable {K} {F : TopCat.Sheaf AddCommGrpCat.{0} X} (a : F ⟶ K.X 0)
  (ha : a ≫ K.d 0 1 = 0)

theorem nativeCechVerticalEdge_refinement :
    FlasqueCechD.abelianCechVerticalEdge U a ha ≫ nativeCechTotalRefinement U V r hr K =
      Cech.AbelianRefinement.nativeCechRefinement U V r hr F.obj ≫ FlasqueCechD.abelianCechVerticalEdge V a ha := by
  apply HomologicalComplex.Hom.ext
  funext p
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    FlasqueCechD.abelianCechVerticalEdge_f, FlasqueCechD.abelianCechVerticalEdge_f, Category.assoc,
    nativeCechTotalRefinement, HomologicalComplex₂.ιTotal_map, ← Category.assoc, ← Category.assoc]
  congr 1
  exact congrArg (fun f => f.f p) (Cech.AbelianRefinement.nativeCechRefinement_naturality U V r hr a.hom)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.CechTotalRefinement

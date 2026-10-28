import OAI.AlgebraicTopology.Sheaf.CohomologySection
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Section Cohomology Sheaf Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SectionCohomologySheafNaturality

noncomputable section

/-! # Naturality of the actual section-complex class in its cohomology sheaf -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex

variable (Y : TopCat.{0}) {K L : CochainComplex (Sheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0})) ℤ}
  (f : K ⟶ L) (n : ℤ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem sectionCohomologySheafificationIso_naturality :
    (presheafToSheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0})).map (homologyMap (((sheafToPresheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0})).mapHomologicalComplex ℤᵘᵖ).map f) n) ≫
      (AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyPresheafSheafificationIso Y L n).hom =
    (AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyPresheafSheafificationIso Y K n).hom ≫ homologyMap f n := by
  let e := NatIso.mapHomologicalComplex
    (asIso (sheafificationAdjunction (Opens.grothendieckTopology Y) (AddCommGrpCat.{0})).counit)
    ℤᵘᵖ
  unfold AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyPresheafSheafificationIso
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  let mf := ((sheafToPresheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0})).mapHomologicalComplex ℤᵘᵖ).map f
  let PK := ((sheafToPresheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0})).mapHomologicalComplex ℤᵘᵖ).obj K
  let PL := ((sheafToPresheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0})).mapHomologicalComplex ℤᵘᵖ).obj L
  have hn : (presheafToSheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0})).map (homologyMap mf n) ≫ ((PL.sc n).mapHomologyIso (presheafToSheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0}))).inv =
      ((PK.sc n).mapHomologyIso (presheafToSheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0}))).inv ≫
        homologyMap (((presheafToSheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0})).mapHomologicalComplex ℤᵘᵖ).map mf) n := by
    simpa only [homologyMap] using!
      ShortComplex.mapHomologyIso_inv_naturality
        ((shortComplexFunctor _ ℤᵘᵖ n).map mf) (presheafToSheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0}))
  have he : homologyMap (((presheafToSheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0})).mapHomologicalComplex ℤᵘᵖ).map mf) n ≫
      homologyMap (e.hom.app L) n =
      homologyMap (e.hom.app K) n ≫ homologyMap f n := by
    simpa only [homologyMap_comp] using! congrArg (fun g => homologyMap g n)
      (e.hom.naturality f)
  calc
    _ = ((PK.sc n).mapHomologyIso (presheafToSheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0}))).inv ≫
        homologyMap (((presheafToSheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0})).mapHomologicalComplex ℤᵘᵖ).map mf) n ≫
        homologyMap (e.hom.app L) n := by
          simpa only [Category.assoc] using! congrArg
            (fun g => g ≫ homologyMap (e.hom.app L) n) hn
    _ = _ := by
      simpa only [Category.assoc] using!
        (congrArg (fun g => ((PK.sc n).mapHomologyIso (presheafToSheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0}))).inv ≫ g) he)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem sectionCohomologyPresheafToSheaf_naturality :
    homologyMap (((sheafToPresheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0})).mapHomologicalComplex ℤᵘᵖ).map f) n ≫
      AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyPresheafToSheaf Y L n =
    AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyPresheafToSheaf Y K n ≫ (homologyMap f n).hom := by
  unfold AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyPresheafToSheaf
  have hu := toSheafify_naturality (Opens.grothendieckTopology Y)
    (homologyMap (((sheafToPresheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0})).mapHomologicalComplex ℤᵘᵖ).map f) n)
  have hn := congrArg (fun g => (sheafToPresheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0})).map g)
    (sectionCohomologySheafificationIso_naturality Y f n)
  calc
    _ = toSheafify (Opens.grothendieckTopology Y) _ ≫
        sheafifyMap (Opens.grothendieckTopology Y)
          (homologyMap (((sheafToPresheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0})).mapHomologicalComplex ℤᵘᵖ).map f) n) ≫
        (AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyPresheafSheafificationIso Y L n).hom.hom := by
          simpa only [Category.assoc] using! congrArg
            (fun g => g ≫
              (AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyPresheafSheafificationIso Y L n).hom.hom) hu
    _ = _ := by
      simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using!
        (congrArg (fun g => toSheafify (Opens.grothendieckTopology Y) _ ≫ g) hn)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem sectionCohomologyToSheafSection_naturality (V : Opens Y) :
    homologyMap (((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex ℤᵘᵖ).map f) n ≫
      AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection Y L n V =
    AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection Y K n V ≫ (homologyMap f n).hom.app (op V) := by
  unfold AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection
  rw [← Category.assoc]
  have he := ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor _ ℤᵘᵖ n).map (((sheafToPresheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0})).mapHomologicalComplex ℤᵘᵖ).map f))
    ((evaluation (Opens Y)ᵒᵖ (AddCommGrpCat.{0})).obj (op V))
  have he' : homologyMap (((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex ℤᵘᵖ).map f) n ≫
      (AlgebraicTopology.Sheaf.CohomologyStalkVanishing.TopCat.sectionCohomologyPresheafOnOpenIso Y L n V).hom =
      (AlgebraicTopology.Sheaf.CohomologyStalkVanishing.TopCat.sectionCohomologyPresheafOnOpenIso Y K n V).hom ≫
      (homologyMap (((sheafToPresheaf (Opens.grothendieckTopology Y) (AddCommGrpCat.{0})).mapHomologicalComplex ℤᵘᵖ).map f) n).app (op V) := by
    simpa only [homologyMap] using! he
  rw [he', Category.assoc]
  have hn := congrArg (fun g => g.app (op V))
    (sectionCohomologyPresheafToSheaf_naturality Y f n)
  simpa only [NatTrans.comp_app, Category.assoc] using!
    (congrArg (fun g => (AlgebraicTopology.Sheaf.CohomologyStalkVanishing.TopCat.sectionCohomologyPresheafOnOpenIso Y K n V).hom ≫ g) hn)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SectionCohomologySheafNaturality

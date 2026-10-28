import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InjectiveSectionsNaturality

/-! # Natural Cohomology Excision -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalCohomologyExcision.IntrinsicCech

noncomputable section

/-! The two-open excision isomorphism is natural in the sheaf. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private def rebundleGroupHom {A B : AddCommGrpCat.{u}} (f : A ⟶ B) :
    AddCommGrpCat.of A ⟶ AddCommGrpCat.of B := AddCommGrpCat.ofHom f.hom

private def cohomologyMap {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ) :
    AddCommGrpCat.of ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{u}).obj F) ⟶
      AddCommGrpCat.of ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{u}).obj G) :=
  rebundleGroupHom ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{u}).map f)

variable {X : TopCat.{u}}

theorem injectiveOpenSectionsRestriction_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    {U V : Opens X} (h : U ≤ V) :
    RestrictedSectionsNaturality.IntrinsicCech.injectiveOpenSectionsMap f V ≫ InjectiveTwoOpenComplex.IntrinsicCech.injectiveOpenSectionsRestriction G h =
      InjectiveTwoOpenComplex.IntrinsicCech.injectiveOpenSectionsRestriction F h ≫ RestrictedSectionsNaturality.IntrinsicCech.injectiveOpenSectionsMap f U := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact ((RestrictedSectionsNaturality.IntrinsicCech.chosenSheafResolutionMap f).f n).hom.naturality (homOfLE h).op |>.symm

def naturalSheafCohomologyTwoOpenExcisionIso
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) (hcover : U ⊔ V = ⊤)
    (hV : ∀ q, Subsingleton (CategoryTheory.Sheaf.H ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat V.isOpenEmbedding).obj F) q))
    (hUV : ∀ q, Subsingleton (CategoryTheory.Sheaf.H
      ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat (U ⊓ V).isOpenEmbedding).obj F) q)) (n : ℕ) :
    AddCommGrpCat.of ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n : _ ⥤ AddCommGrpCat.{u}).obj F) ≅
      AddCommGrpCat.of ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology U) n : _ ⥤ AddCommGrpCat.{u}).obj ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat U.isOpenEmbedding).obj F)) := by
  have : QuasiIso (InjectiveTwoOpenComplex.IntrinsicCech.injectiveOpenSectionsRestriction F (show U ≤ ⊤ from le_top)) := by
    have hh : ∀ (h : U ≤ U ⊔ V), QuasiIso (InjectiveTwoOpenComplex.IntrinsicCech.injectiveOpenSectionsRestriction F h) :=
      fun _ => InjectiveTwoOpenComplex.IntrinsicCech.injectiveOpenSectionsRestriction_quasiIso F U V hV hUV
    rw [hcover] at hh
    exact hh le_top
  exact (HilbertConstruction.Sheaf.CohomologyExcision.IntrinsicCech.injectiveGlobalSectionsCohomologyIso F n).symm ≪≫
    asIso (HomologicalComplex.homologyMap
      (InjectiveTwoOpenComplex.IntrinsicCech.injectiveOpenSectionsRestriction F (show U ≤ ⊤ from le_top)) n) ≪≫
    InjectiveSectionsNaturality.IntrinsicCech.naturalInjectiveOpenSectionsCohomologyIso F U n

private theorem iso_square_inv
    {A B C D : AddCommGrpCat.{u}} (e : A ≅ B) (d : C ≅ D)
    (a : A ⟶ C) (b : B ⟶ D) (h : a ≫ d.hom = e.hom ≫ b) :
    b ≫ d.inv = e.inv ≫ a := by
  calc
    _ = e.inv ≫ (e.hom ≫ b) ≫ d.inv := by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = e.inv ≫ (a ≫ d.hom) ≫ d.inv := by rw [← h]
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem naturalSheafCohomologyTwoOpenExcisionIso_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (U V : Opens X) (hcover : U ⊔ V = ⊤)
    (hFV : ∀ q, Subsingleton (CategoryTheory.Sheaf.H ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat V.isOpenEmbedding).obj F) q))
    (hFUV : ∀ q, Subsingleton (CategoryTheory.Sheaf.H
      ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat (U ⊓ V).isOpenEmbedding).obj F) q))
    (hGV : ∀ q, Subsingleton (CategoryTheory.Sheaf.H ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat V.isOpenEmbedding).obj G) q))
    (hGUV : ∀ q, Subsingleton (CategoryTheory.Sheaf.H
      ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat (U ⊓ V).isOpenEmbedding).obj G) q)) (n : ℕ) :
    cohomologyMap f n ≫
        (naturalSheafCohomologyTwoOpenExcisionIso G U V hcover hGV hGUV n).hom =
      (naturalSheafCohomologyTwoOpenExcisionIso F U V hcover hFV hFUV n).hom ≫
        cohomologyMap ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat U.isOpenEmbedding).map f) n := by
  let aF := HilbertConstruction.Sheaf.CohomologyExcision.IntrinsicCech.injectiveGlobalSectionsCohomologyIso F n
  let aG := HilbertConstruction.Sheaf.CohomologyExcision.IntrinsicCech.injectiveGlobalSectionsCohomologyIso G n
  let bF := HomologicalComplex.homologyMap
    (InjectiveTwoOpenComplex.IntrinsicCech.injectiveOpenSectionsRestriction F (show U ≤ ⊤ from le_top)) n
  let bG := HomologicalComplex.homologyMap
    (InjectiveTwoOpenComplex.IntrinsicCech.injectiveOpenSectionsRestriction G (show U ≤ ⊤ from le_top)) n
  let cF := InjectiveSectionsNaturality.IntrinsicCech.naturalInjectiveOpenSectionsCohomologyIso F U n
  let cG := InjectiveSectionsNaturality.IntrinsicCech.naturalInjectiveOpenSectionsCohomologyIso G U n
  let mt := HomologicalComplex.homologyMap (RestrictedSectionsNaturality.IntrinsicCech.injectiveOpenSectionsMap f ⊤) n
  let mu := HomologicalComplex.homologyMap (RestrictedSectionsNaturality.IntrinsicCech.injectiveOpenSectionsMap f U) n
  have ha : cohomologyMap f n ≫ aG.inv = aF.inv ≫ mt :=
    iso_square_inv aF aG mt _ (InjectiveSectionsNaturality.IntrinsicCech.injectiveGlobalSectionsCohomologyIso_naturality f n)
  have hb : mt ≫ bG = bF ≫ mu := by
    have h := congrArg (fun k => HomologicalComplex.homologyMap k n)
      (injectiveOpenSectionsRestriction_naturality f (show U ≤ ⊤ from le_top))
    simpa only [HomologicalComplex.homologyMap_comp] using h
  have hc : mu ≫ cG.hom = cF.hom ≫ cohomologyMap ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat U.isOpenEmbedding).map f) n :=
    InjectiveSectionsNaturality.IntrinsicCech.naturalInjectiveOpenSectionsCohomologyIso_naturality f U n
  change cohomologyMap f n ≫ (aG.inv ≫ bG ≫ cG.hom) =
    (aF.inv ≫ bF ≫ cF.hom) ≫ _
  calc
    _ = aF.inv ≫ (mt ≫ bG) ≫ cG.hom := by
      rw [← Category.assoc, ha]
      simp only [Category.assoc]
    _ = aF.inv ≫ (bF ≫ mu) ≫ cG.hom := by rw [hb]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun k => aF.inv ≫ bF ≫ k) hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalCohomologyExcision.IntrinsicCech

import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientHomologyNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.FunctorTransformation
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.InjectiveRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationNaturality

/-! # Single Coefficient Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SingleCoefficientCoordinates

noncomputable section

/-! The original supported single-module total is identified with the
actual additive sheaf-section total. These coordinates preserve both
coefficient morphisms and restriction between diagrams of opens. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v w
variable {C : Type} [Preorder C] [HasFiniteProducts C]
  {ι : Type} [LinearOrder ι] (W : ι → C)

private abbrev totalH (D : Type v) [Category.{w} D] [Abelian D]
    [HasProducts.{0} D] [HasCoproducts.{0} D] (q : ℕ) :
    CochainComplex (Cᵒᵖ ⥤ D) ℕ ⥤ D :=
  (AugmentedOrdered.CechFunctor.functor W).mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ) ⋙
      HomologicalComplex.homologyFunctor D (.up ℕ) q

def singleH (D : Type v) [Category.{w} D] [Abelian D]
    [HasProducts.{0} D] [HasCoproducts.{0} D] (c q : ℕ) : (Cᵒᵖ ⥤ D) ⥤ D :=
  single (Cᵒᵖ ⥤ D) (.up ℕ) c ⋙ totalH W D q

variable (A : Type) [CommRing A]

private abbrev forgetScalars : ModuleCat.{0} A ⥤ AddCommGrpCat.{0} := forget₂ _ _
private abbrev forgetDiagrams : (Cᵒᵖ ⥤ ModuleCat.{0} A) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{0}) :=
  (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{0} A) AddCommGrpCat.{0}).obj (forgetScalars A)

local instance : HasFiniteBiproducts (ModuleCat.{0} A) := Abelian.hasFiniteBiproducts

def forgetIso (P : Cᵒᵖ ⥤ ModuleCat.{0} A) (c q : ℕ) :
    (forgetScalars A).obj ((singleH W (ModuleCat.{0} A) c q).obj P) ≅
      (singleH W AddCommGrpCat c q).obj (P ⋙ forgetScalars A) :=
  AugmentedCech.CoefficientTotal.homologyIso W (forgetScalars A)
      ((single _ (.up ℕ) c).obj P) q ≪≫
    (totalH W AddCommGrpCat q).mapIso
      ((singleMapHomologicalComplex (forgetDiagrams (C := C) A) (.up ℕ) c).app P)

theorem forgetIso_natural {P Q : Cᵒᵖ ⥤ ModuleCat.{0} A} (a : P ⟶ Q) (c q : ℕ) :
    (forgetScalars A).map ((singleH W (ModuleCat.{0} A) c q).map a) ≫
        (forgetIso W A Q c q).hom =
      (forgetIso W A P c q).hom ≫
        (singleH W AddCommGrpCat c q).map (Functor.whiskerRight a (forgetScalars A)) := by
  have h₁ := AugmentedCech.CoefficientHomologyNaturality.Total.homologyIso_naturality W (forgetScalars A)
    ((single _ (.up ℕ) c).map a) q
  have h₂ := congrArg (totalH W AddCommGrpCat q).map
    ((singleMapHomologicalComplex (forgetDiagrams (C := C) A) (.up ℕ) c).hom.naturality a)
  simp only [CategoryTheory.Functor.map_comp] at h₂
  exact DualComplexHomology.compose_squares _ _ _ _ _ _ _ h₁ h₂

variable {Y : Scheme.{0}} (F : C ⥤ Y.Opens) (N : Y.Modules)

private abbrev sections (M : Y.Modules) : Y.Opensᵒᵖ ⥤ AddCommGrpCat :=
  ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M).obj

def sourceIso (c q : ℕ) :
    (singleH W AddCommGrpCat c q).obj (F.op ⋙ sections N) ≅
      (AffinePrincipal.Injective.Comparison.source F W N c).homology q :=
  ((totalH W AddCommGrpCat q).mapIso
    ((singleMapHomologicalComplex (AffinePrincipal.Injective.Comparison.coefficients F)
      (.up ℕ) c).app ((SheafOfModules.toSheaf Y.ringCatSheaf).obj N))).symm

theorem sourceIso_natural {M : Y.Modules} (a : N ⟶ M) (c q : ℕ) :
    (singleH W AddCommGrpCat c q).map
        (Functor.whiskerLeft F.op ((SheafOfModules.toSheaf Y.ringCatSheaf).map a).hom) ≫
      (sourceIso W F M c q).hom =
    (sourceIso W F N c q).hom ≫
      homologyMap (AffinePrincipal.Injective.Comparison.sourceMap F W N c a) q := by
  have h := congrArg (totalH W AddCommGrpCat q).map
    ((singleMapHomologicalComplex (AffinePrincipal.Injective.Comparison.coefficients F)
      (.up ℕ) c).hom.naturality ((SheafOfModules.toSheaf Y.ringCatSheaf).map a))
  simp only [CategoryTheory.Functor.map_comp] at h
  exact CohomologyConcentrationNaturality.inverse_square _ _
    ((sourceIso W F N c q).symm) ((sourceIso W F M c q).symm) h

theorem sourceIso_restriction (G : C ⥤ Y.Opens) (α : G ⟶ F) (c q : ℕ) :
    (singleH W AddCommGrpCat c q).map (Functor.whiskerRight (NatTrans.op α) (sections N)) ≫
        (sourceIso W G N c q).hom =
      (sourceIso W F N c q).hom ≫
        homologyMap (AffinePrincipal.InjectiveRestriction.sourceMap F G α W N c) q := by
  have h := congrArg (totalH W AddCommGrpCat q).map
    (Single.FunctorTransformation.naturality
      (AffinePrincipal.Injective.Comparison.coefficients F)
      (AffinePrincipal.Injective.Comparison.coefficients G)
      (AffinePrincipal.InjectiveRestriction.coefficientsMap F G α)
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj N) c)
  simp only [CategoryTheory.Functor.map_comp] at h
  exact CohomologyConcentrationNaturality.inverse_square _ _
    ((sourceIso W F N c q).symm) ((sourceIso W G N c q).symm) h

variable (P : Cᵒᵖ ⥤ ModuleCat.{0} A) (e : P ⋙ forgetScalars A ≅ F.op ⋙ sections N)

def iso (c q : ℕ) :
    (forgetScalars A).obj ((singleH W (ModuleCat.{0} A) c q).obj P) ≅
      (AffinePrincipal.Injective.Comparison.source F W N c).homology q :=
  forgetIso W A P c q ≪≫ (singleH W AddCommGrpCat c q).mapIso e ≪≫ sourceIso W F N c q

theorem coefficient_natural {Q : Cᵒᵖ ⥤ ModuleCat.{0} A} {M : Y.Modules}
    (d : Q ⋙ forgetScalars A ≅ F.op ⋙ sections M) (a : P ⟶ Q) (b : N ⟶ M)
    (h : Functor.whiskerRight a (forgetScalars A) ≫ d.hom =
      e.hom ≫ Functor.whiskerLeft F.op ((SheafOfModules.toSheaf Y.ringCatSheaf).map b).hom)
    (c q : ℕ) :
    (forgetScalars A).map ((singleH W (ModuleCat.{0} A) c q).map a) ≫ (iso W A F M Q d c q).hom =
      (iso W A F N P e c q).hom ≫
        homologyMap (AffinePrincipal.Injective.Comparison.sourceMap F W N c b) q := by
  have h₂ := congrArg (singleH W AddCommGrpCat c q).map h
  simp only [CategoryTheory.Functor.map_comp] at h₂
  have h₁₂ := DualComplexHomology.compose_squares _ _ _ _ _ _ _
    (forgetIso_natural W A a c q) h₂
  have h₃ := sourceIso_natural W F N b c q
  simpa only [iso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using
    DualComplexHomology.compose_squares _ _ _ _ _ _ _ h₁₂ h₃

theorem restriction_natural (G : C ⥤ Y.Opens) (α : G ⟶ F)
    {Q : Cᵒᵖ ⥤ ModuleCat.{0} A} (d : Q ⋙ forgetScalars A ≅ G.op ⋙ sections N)
    (a : P ⟶ Q)
    (h : Functor.whiskerRight a (forgetScalars A) ≫ d.hom =
      e.hom ≫ Functor.whiskerRight (NatTrans.op α) (sections N)) (c q : ℕ) :
    (forgetScalars A).map ((singleH W (ModuleCat.{0} A) c q).map a) ≫ (iso W A G N Q d c q).hom =
      (iso W A F N P e c q).hom ≫
        homologyMap (AffinePrincipal.InjectiveRestriction.sourceMap F G α W N c) q := by
  have h₂ := congrArg (singleH W AddCommGrpCat c q).map h
  simp only [CategoryTheory.Functor.map_comp] at h₂
  have h₁₂ := DualComplexHomology.compose_squares _ _ _ _ _ _ _
    (forgetIso_natural W A a c q) h₂
  have h₃ := sourceIso_restriction W F N G α c q
  simpa only [iso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using
    DualComplexHomology.compose_squares _ _ _ _ _ _ _ h₁₂ h₃

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SingleCoefficientCoordinates

import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechOpenEquality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechMapReindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechPrecompose

/-! # Cech Coefficient Reindex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechCoefficientReindex

noncomputable section

/-! Coefficient transport and a genuine change of principal indices preserve
 the original supported comparison to bounded crystalline cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteProducts r]
  (F₁ : C ⥤ Y.Opens) (F₂ : D ⥤ Y.Opens) (hF : F₁ = r ⋙ F₂)
  {ι : Type u} [LinearOrder ι] (U : ι → C)

local instance coefficient_limits : HasLimitsOfSize.{u, u}
    (ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B))) :=
  ModuleCat.hasLimitsOfSize.{u, u, u+2, u+1}
local instance coefficient_colimits : HasColimitsOfSize.{0, 0}
    (ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B))) :=
  ModuleCat.hasColimitsOfSize.{u+2, u+1, 0, 0} _

variable
  (L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u+2}
    (Crystalline.ExactRestriction.Coeff (B := B))) ℕ)
  (M : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{u+2}
    (Crystalline.ExactRestriction.Coeff (B := B))) ℕ)
  (c : L ⟶ CechMapReindex.pulledSource r M)
  (a : M ⟶ Supported.OrderedCechEdge.presheafComplex.{u+1,u,u,u+2}
    (Crystalline.ExactRestriction.Coeff (B := B)) Y.carrier F₂
    (BoundedOpen.FlasqueComplex.complex fY n I))

def coefficientMap : L ⟶
    Supported.OrderedCechEdge.presheafComplex.{u+1,u,u,u+2}
      (Crystalline.ExactRestriction.Coeff (B := B)) Y.carrier F₁
      (BoundedOpen.FlasqueComplex.complex fY n I) :=
  CechOpenEquality.transport fY n I (r ⋙ F₂) F₁ hF.symm L
    (c ≫ CechMapReindex.pulledMap fY n I r F₂ M a)

def sourceMap : (AugmentedOrdered.CechFunctor.bicomplex U L).total (.up ℕ) ⟶
    (AugmentedOrdered.CechFunctor.bicomplex (r.obj ∘ U) M).total (.up ℕ) :=
  AugmentedOrdered.CechForgetNaturality.map U c ≫
    (CechMapReindex.sourceIso r U M).hom

variable (O : Y.Opens)
  (hO₁ : ∀ j, F₁.obj (U j) ≤ O)
  (hO₂ : ∀ j, F₂.obj (r.obj (U j)) ≤ O)
  (hcover₁ : F₁.obj (⊤_ C) ⊓ O ≤ ⨆ j, F₁.obj (U j))
  (hcover₂ : F₂.obj (⊤_ D) ⊓ O ≤ ⨆ j, F₂.obj (r.obj (U j)))
  (hrows₁ : ∀ q m, ((Cech.bicomplex fY n I F₁ U).X q).ExactAt (m+1))
  (hrows₂ : ∀ q m,
    ((Cech.bicomplex fY n I F₂ (r.obj ∘ U)).X q).ExactAt (m+1))
  (hglobal₁ : F₁.obj (⊤_ C) ⊔ O = ⊤)
  (hglobal₂ : F₂.obj (⊤_ D) ⊔ O = ⊤)

theorem comparison (i : ℕ) :
    Cech.map fY n I F₁ U O hO₁ hcover₁ hrows₁ hglobal₁ L
      (coefficientMap fY n I r F₁ F₂ hF L M c a) i =
    HomologicalComplex.homologyMap (sourceMap r U L M c) i ≫
      Cech.map fY n I F₂ (r.obj ∘ U) O hO₂ hcover₂ hrows₂ hglobal₂ M a i := by
  have hcoverR : (r ⋙ F₂).obj (⊤_ C) ⊓ O ≤ ⨆ j, F₂.obj (r.obj (U j)) := by
    simpa only [hF, Functor.comp_obj] using hcover₁
  have hrowsR (q m : ℕ) :
      ((Cech.bicomplex fY n I (r ⋙ F₂) U).X q).ExactAt (m+1) := by
    rw [← hF]
    exact hrows₁ q m
  have hglobalR : (r ⋙ F₂).obj (⊤_ C) ⊔ O = ⊤ := by
    rw [← hF]
    exact hglobal₁
  have hopen := CechOpenEquality.comparison fY n I (r ⋙ F₂) F₁ hF.symm U L
    (c ≫ CechMapReindex.pulledMap fY n I r F₂ M a)
    O hO₂ hO₁ hcoverR hcover₁ hrowsR hrows₁ hglobalR hglobal₁ i
  have hpre := CechPrecompose.comparison fY n I (r ⋙ F₂) U O
    hO₂ hcoverR hrowsR hglobalR c
    (CechMapReindex.pulledMap fY n I r F₂ M a) i
  have hreindex := CechMapReindex.comparison fY n I r F₂ U M a O
    hO₂ hcoverR hcover₂ hrowsR hrows₂ hglobalR hglobal₂ i
  calc
    Cech.map fY n I F₁ U O hO₁ hcover₁ hrows₁ hglobal₁ L
        (coefficientMap fY n I r F₁ F₂ hF L M c a) i =
      Cech.map fY n I (r ⋙ F₂) U O hO₂ hcoverR hrowsR hglobalR L
        (c ≫ CechMapReindex.pulledMap fY n I r F₂ M a) i := hopen.symm
    _ = HomologicalComplex.homologyMap (AugmentedOrdered.CechForgetNaturality.map U c) i ≫
      Cech.map fY n I (r ⋙ F₂) U O hO₂ hcoverR hrowsR hglobalR
        (CechMapReindex.pulledSource r M)
        (CechMapReindex.pulledMap fY n I r F₂ M a) i := hpre
    _ = HomologicalComplex.homologyMap (AugmentedOrdered.CechForgetNaturality.map U c) i ≫
      (HomologicalComplex.homologyMap (CechMapReindex.sourceIso r U M).hom i ≫
        Cech.map fY n I F₂ (r.obj ∘ U) O hO₂ hcover₂ hrows₂ hglobal₂ M a i) :=
      congrArg (fun b => HomologicalComplex.homologyMap
        (AugmentedOrdered.CechForgetNaturality.map U c) i ≫ b) hreindex.symm
    _ = HomologicalComplex.homologyMap (sourceMap r U L M c) i ≫
      Cech.map fY n I F₂ (r.obj ∘ U) O hO₂ hcover₂ hrows₂ hglobal₂ M a i := by
      simp only [sourceMap, HomologicalComplex.homologyMap_comp, Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechCoefficientReindex

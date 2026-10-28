import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.TypedMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.Pushforward
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.OpenBaseChangeNaturality
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OrderedCechNaturality

/-! # Pushforward Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PushforwardNaturality

noncomputable section

/-! The actual inverse-cover to pushforward Čech comparison is
natural in its coefficient module. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem compose {C : Type*} [Category C] {A B D A' B' D' : C}
    (e : A ⟶ B) (e' : A' ⟶ B') (s : B ⟶ D) (s' : B' ⟶ D')
    (a : A ⟶ A') (b : B ⟶ B') (d : D ⟶ D')
    (h : a ≫ e' = e ≫ b) (h' : b ≫ s' = s ≫ d) :
    a ≫ (e' ≫ s') = (e ≫ s) ≫ d := by
  rw [← Category.assoc, h, Category.assoc, h', ← Category.assoc]

theorem inverse {C : Type*} [Category C] {A B A' B' : C}
    (e : A ≅ B) (e' : A' ≅ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ e'.hom = e.hom ≫ b) : b ≫ e'.inv = e.inv ≫ a := by
  apply (cancel_epi e.hom).1
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  {ι : Type u} (U : ι → Y.left.Opens) {M N : X.left.Modules} (a : M ⟶ N)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality.forgetCoefficients R
local notation "J" => OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of R))
local notation "F" => Opens.map f.left.base
local notation "V" => (fun i => CategoryTheory.Functor.obj (Opens.map f.left.base) (U i))
local notation "a'" => CategoryTheory.Functor.map (Scheme.Modules.pushforward f.left) a
local instance opens_finiteLimits : PreservesFiniteLimits (Opens.map f.left.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.left.base.frameHom).toFunctor
  infer_instance

def baseMap :
    AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex Y.hom ((Scheme.Modules.pushforward f.left).obj M) U ⟶
      AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex Y.hom ((Scheme.Modules.pushforward f.left).obj N) U :=
  TypedMap.map Y.hom U (a')

def targetMap :
    ((J).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex Y.hom ((Scheme.Modules.pushforward f.left).obj M) U) ⟶
    ((J).mapHomologicalComplex (.up ℕ)).obj
      (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex Y.hom ((Scheme.Modules.pushforward f.left).obj N) U) :=
  ((J).mapHomologicalComplex (.up ℕ)).map (baseMap R X Y f U a)

theorem complex_naturality :
    ((G).mapHomologicalComplex (.up ℕ)).map (CohomologyNaturality.map R X V a) ≫
      (Pushforward.Comparison.complexIso R X Y f N U).hom =
    (Pushforward.Comparison.complexIso R X Y f M U).hom ≫
      targetMap R X Y f U a := by
  have h₁ := CohomologyNaturality.forget_natural R X V a
  have h₂ := inverse (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (F) U M.presheaf)
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (F) U N.presheaf) _ _
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.OpenBaseChangeNaturality.CechOpenBaseChangeNaturality.naturality (F) U
      ((SheafOfModules.toSheaf X.left.ringCatSheaf).map a).hom)
  have h₃ := inverse
    (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso Y.hom ((Scheme.Modules.pushforward f.left).obj M) U)
    (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso Y.hom ((Scheme.Modules.pushforward f.left).obj N) U) _ _
    (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso_naturality Y.hom (a') U)
  have h₁₂ := compose
    (DimensionBound.forgetIso R X M V).hom
    (DimensionBound.forgetIso R X N V).hom
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (F) U M.presheaf).inv
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (F) U N.presheaf).inv _ _ _ h₁ h₂
  exact compose
    ((DimensionBound.forgetIso R X M V).hom ≫ (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (F) U M.presheaf).inv)
    ((DimensionBound.forgetIso R X N V).hom ≫ (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (F) U N.presheaf).inv)
    (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso Y.hom ((Scheme.Modules.pushforward f.left).obj M) U).inv
    (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso Y.hom ((Scheme.Modules.pushforward f.left).obj N) U).inv
    _ _ _ h₁₂ h₃

variable [LinearOrder ι]

theorem cohomology_naturality (n : ℕ) :
    (G).map (HomologicalComplex.homologyMap (CohomologyNaturality.map R X V a) n) ≫
      (Pushforward.Comparison.cohomologyIso R X Y f N U n).hom =
    (Pushforward.Comparison.cohomologyIso R X Y f M U n).hom ≫
      (J).map (HomologicalComplex.homologyMap
        ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor Y.hom U).map (a')) n) := by
  have h₁ := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n).map
      (CohomologyNaturality.map R X V a)) (G)
  change (G).map (HomologicalComplex.homologyMap (CohomologyNaturality.map R X V a) n) ≫
      (((DimensionBound.complex R X N V).sc n).mapHomologyIso (G)).inv =
    (((DimensionBound.complex R X M V).sc n).mapHomologyIso (G)).inv ≫
      HomologicalComplex.homologyMap (((G).mapHomologicalComplex (.up ℕ)).map
        (CohomologyNaturality.map R X V a)) n at h₁
  have h₂ := congrArg (fun z => HomologicalComplex.homologyMap z n)
    (complex_naturality R X Y f U a)
  simp only [HomologicalComplex.homologyMap_comp] at h₂
  have h₃ := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) n).map
      ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor Y.hom U).map (a'))) (J)
  have h₄ := congrArg (J).map
    (ArithmeticGeometry.OrdinaryLocus.Openness.OrderedCechNaturality.Construction.baseCechOrderedHomologyIso_naturality Y.hom (a') U n)
  simp only [Functor.map_comp] at h₄
  have h₁₂ := compose
    (((DimensionBound.complex R X M V).sc n).mapHomologyIso (G)).inv
    (((DimensionBound.complex R X N V).sc n).mapHomologyIso (G)).inv
    (HomologicalComplex.homologyMap (Pushforward.Comparison.complexIso R X Y f M U).hom n)
    (HomologicalComplex.homologyMap (Pushforward.Comparison.complexIso R X Y f N U).hom n)
    _ _ _ h₁ h₂
  have h₃₄ := compose
    (((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex Y.hom ((Scheme.Modules.pushforward f.left).obj M) U).sc n).mapHomologyIso (J)).hom
    (((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex Y.hom ((Scheme.Modules.pushforward f.left).obj N) U).sc n).mapHomologyIso (J)).hom
    ((J).map (AlgebraicGeometry.SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomologyIso Y.hom ((Scheme.Modules.pushforward f.left).obj M) U n).hom)
    ((J).map (AlgebraicGeometry.SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomologyIso Y.hom ((Scheme.Modules.pushforward f.left).obj N) U n).hom)
    _ _ _ h₃ h₄
  have h := compose _ _ _ _ _ _ _ h₁₂ h₃₄
  simpa only [Pushforward.Comparison.cohomologyIso, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.homologyMapIso_hom, Functor.mapIso_hom, Category.assoc] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PushforwardNaturality

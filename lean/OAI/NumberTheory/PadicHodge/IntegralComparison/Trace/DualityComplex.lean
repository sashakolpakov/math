import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityDescent
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactModuleDualFunctor
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Category.Grp.Limits

/-! # Duality Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityComplex

noncomputable section

/-! A trace pairing gives a natural map from representable morphisms to
the coefficient dual. Termwise perfectness gives an isomorphism of the
actual mapped complexes, with their existing differentials. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v
variable {C : Type v} [Category.{u} C] [Preadditive C]
  (R : Type u) [CommRing R]
  (F : C ⥤ ModuleCat.{u} R) [F.Additive]
  {ω : C} (τ : F.obj ω ⟶ ModuleCat.of R R)

def dualFunctor : Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  F.op ⋙ ExactModuleDualFunctor.functor R ⋙ forget₂ (ModuleCat R) AddCommGrpCat

instance : (dualFunctor R F).Additive := by
  unfold dualFunctor
  infer_instance

def pairing : preadditiveYoneda.obj ω ⟶ dualFunctor R F where
  app M := AddCommGrpCat.ofHom {
    toFun f := (DualityDescent.pairingMap F τ M.unop f).hom
    map_zero' := by
      change (F.map (0 : M.unop ⟶ ω) ≫ τ).hom = 0
      rw [F.map_zero, zero_comp]
      rfl
    map_add' f g := by
      change (F.map (f + g) ≫ τ).hom = (F.map f ≫ τ).hom + (F.map g ≫ τ).hom
      rw [F.map_add, Preadditive.add_comp]
      rfl }
  naturality {M N} f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro g
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom
      (DualityDescent.pairingMap_comp F τ f.unop g) x

@[simp] theorem pairing_apply (M : Cᵒᵖ) (f : M.unop ⟶ ω) :
    (pairing R F τ).app M f = (F.map f ≫ τ).hom := rfl

theorem pairing_bijective (M : Cᵒᵖ)
    (h : Function.Bijective (DualityDescent.pairingMap F τ M.unop)) :
    Function.Bijective ((pairing R F τ).app M) :=
  ModuleCat.homEquiv.bijective.comp h

def complexMap {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex Cᵒᵖ c) :
    ((preadditiveYoneda.obj ω).mapHomologicalComplex c).obj K ⟶
      ((dualFunctor R F).mapHomologicalComplex c).obj K :=
  ((pairing R F τ).mapHomologicalComplex c).app K

@[simp] theorem complexMap_f {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex Cᵒᵖ c) (i : ι) :
    (complexMap R F τ c K).f i = (pairing R F τ).app (K.X i) := rfl

theorem complexMap_isIso {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex Cᵒᵖ c)
    (h : ∀ i, Function.Bijective (DualityDescent.pairingMap F τ (K.X i).unop)) :
    IsIso (complexMap R F τ c K) := by
  let (i : ι) : IsIso ((complexMap R F τ c K).f i) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (pairing_bijective R F τ (K.X i) (h i))
  exact HomologicalComplex.Hom.isIso_of_components _

def complexIso {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex Cᵒᵖ c)
    (h : ∀ i, Function.Bijective (DualityDescent.pairingMap F τ (K.X i).unop)) :
    ((preadditiveYoneda.obj ω).mapHomologicalComplex c).obj K ≅
      ((dualFunctor R F).mapHomologicalComplex c).obj K := by
  letI := complexMap_isIso R F τ c K h
  exact asIso (complexMap R F τ c K)

@[simp] theorem complexIso_hom {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex Cᵒᵖ c)
    (h : ∀ i, Function.Bijective (DualityDescent.pairingMap F τ (K.X i).unop)) :
    (complexIso R F τ c K h).hom = complexMap R F τ c K := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityComplex

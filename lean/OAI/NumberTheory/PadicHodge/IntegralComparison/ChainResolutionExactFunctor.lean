import OAI.NumberTheory.PadicHodge.IntegralComparison.ChainResolutionOpposite
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Chain Resolution Exact Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ChainResolutionExactFunctor

noncomputable section

/-! Exact functors preserve the original augmented chain resolutions and their degree-zero augmentations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (P : ChainComplex C ℕ) {Z : C} (ε : P ⟶ (ChainComplex.single₀ C).obj Z)

def augmentation : (F.mapHomologicalComplex (.down ℕ)).obj P ⟶ (ChainComplex.single₀ D).obj (F.obj Z) :=
  (F.mapHomologicalComplex (.down ℕ)).map ε ≫
    (HomologicalComplex.singleMapHomologicalComplex F (.down ℕ) 0).hom.app Z

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
theorem augmentation_zero : (augmentation F P ε).f 0 = F.map (ε.f 0) := by
  change F.map (ε.f 0) ≫ 𝟙 _ = _
  exact Category.comp_id _

instance augmentation_quasiIso [QuasiIso ε] : QuasiIso (augmentation F P ε) := by
  let h : QuasiIso ((F.mapHomologicalComplex (.down ℕ)).map ε) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology ε F
  let e := (HomologicalComplex.singleMapHomologicalComplex F (.down ℕ) 0).app Z
  let he : QuasiIso e.hom := quasiIso_of_isIso _
  exact quasiIso_comp _ _ (hφ := h) (hφ' := he)

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
theorem opposite_augmentation_zero :
    (ChainResolutionOpposite.augmentation ((F.mapHomologicalComplex (.down ℕ)).obj P) (augmentation F P ε)).f 0 =
      F.op.map ((ChainResolutionOpposite.augmentation P ε).f 0) :=
  (ChainResolutionOpposite.augmentation_zero _ _).trans
    ((congrArg Quiver.Hom.op (augmentation_zero F P ε)).trans
      (congrArg F.op.map (ChainResolutionOpposite.augmentation_zero P ε).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ChainResolutionExactFunctor

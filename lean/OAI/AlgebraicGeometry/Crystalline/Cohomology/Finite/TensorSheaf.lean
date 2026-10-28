import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TensorInverseLimit
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.Whiskering

/-! # Tensor Sheaf -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TensorSheaf.FiniteTensorSheaf

noncomputable section

/-!
# Tensoring sheaf sections with a finite free coefficient module

A chosen finite basis identifies tensoring with a power functor, namely
the limit of a constant finite diagram. This proves preservation of
limits at every index size, including the sizes of native site covers.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u v w

variable (R ξ V : Type u) [CommRing R] [Fintype ξ] [AddCommGroup V] [Module R V]
  (b : Module.Basis ξ R V)

def tensor : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  MonoidalCategory.tensorRight (ModuleCat.of R V)

def power : ModuleCat.{u} R ⥤ ModuleCat.{u} R := Functor.const (Discrete ξ) ⋙ lim

def coordinate (M : ModuleCat.{u} R) (i : ξ) : (tensor R V).obj M ⟶ M :=
  ModuleCat.ofHom ((LinearMap.proj i).comp
    (TensorInverseLimit.FiniteTensorInverseLimit.coordinateEquiv R ξ M V b).toLinearMap)

def cone (M : ModuleCat.{u} R) : Cone ((Functor.const (Discrete ξ)).obj M) where
  pt := (tensor R V).obj M
  π :=
    { app i := coordinate R ξ V b M i.as
      naturality := by
        intro i j f
        have h : i = j := Discrete.ext (Discrete.eq_of_hom f)
        subst j
        simp }

def coneIsLimit (M : ModuleCat.{u} R) : IsLimit (cone R ξ V b M) where
  lift s := ModuleCat.ofHom ((TensorInverseLimit.FiniteTensorInverseLimit.coordinateEquiv R ξ M V b).symm.toLinearMap.comp
    (LinearMap.pi (fun i => (s.π.app ⟨i⟩).hom)))
  fac s i := by
    apply ModuleCat.hom_ext
    ext x
    exact congrFun ((TensorInverseLimit.FiniteTensorInverseLimit.coordinateEquiv R ξ M V b).apply_symm_apply
      (fun i => s.π.app ⟨i⟩ x)) i.as
  uniq s m hm := by
    apply ModuleCat.hom_ext
    ext x
    apply (TensorInverseLimit.FiniteTensorInverseLimit.coordinateEquiv R ξ M V b).injective
    funext i
    exact (congrArg (fun f => f x) (hm ⟨i⟩)).trans
      (congrFun ((TensorInverseLimit.FiniteTensorInverseLimit.coordinateEquiv R ξ M V b).apply_symm_apply
        (fun j => s.π.app ⟨j⟩ x)) i).symm

def componentIso (M : ModuleCat.{u} R) : (tensor R V).obj M ≅ (power R ξ).obj M :=
  (coneIsLimit R ξ V b M).conePointUniqueUpToIso (limit.isLimit _)

theorem component_pi (M : ModuleCat.{u} R) (i : Discrete ξ) :
    (componentIso R ξ V b M).hom ≫ limit.π ((Functor.const (Discrete ξ)).obj M) i =
      coordinate R ξ V b M i.as :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ i

theorem coordinate_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) (i : ξ) :
    (tensor R V).map f ≫ coordinate R ξ V b N i = coordinate R ξ V b M i ≫ f := by
  apply ModuleCat.hom_ext
  ext x
  exact congrFun (LinearMap.congr_fun
    (TensorInverseLimit.FiniteTensorInverseLimit.coordinate_naturality R ξ M N V b f.hom) x) i

def functorIso : tensor R V ≅ power R ξ :=
  NatIso.ofComponents (componentIso R ξ V b) (by
    intro M N f
    apply limit.hom_ext
    intro i
    have hl := limMap_π ((Functor.const (Discrete ξ)).map f) i
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun g => (tensor R V).map f ≫ g) (component_pi R ξ V b N i)).trans
        ((coordinate_naturality R ξ V b f i.as).trans
          ((congrArg (fun g => g ≫ f) (component_pi R ξ V b M i)).symm.trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun g => (componentIso R ξ V b M).hom ≫ g) hl).symm.trans
                (Category.assoc _ _ _).symm))))))

instance power_preservesLimits : PreservesLimitsOfSize.{w, v} (power R ξ) := by
  dsimp [power]
  infer_instance

include b in
theorem tensor_preservesLimits : PreservesLimitsOfSize.{w, v} (tensor R V) :=
  preservesLimits_of_natIso (functorIso R ξ V b).symm

include b in
theorem isSheaf {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ ModuleCat.{u} R) (hP : Presheaf.IsSheaf J P) :
    Presheaf.IsSheaf J (P ⋙ tensor R V) := by
  have : PreservesLimitsOfSize.{w, max v w} (tensor R V) := tensor_preservesLimits R ξ V b
  exact Presheaf.isSheaf_comp_of_isSheaf J P (tensor R V) hP

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TensorSheaf.FiniteTensorSheaf

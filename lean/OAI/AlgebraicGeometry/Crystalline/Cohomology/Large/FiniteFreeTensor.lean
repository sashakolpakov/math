import OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.FiniteTensorCoordinates
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Finite Free Tensor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.FiniteFreeTensor.LargeFiniteFreeTensor

noncomputable section

/-!
# Finite free coefficients preserve limits of large modules

The coefficient basis identifies tensoring the original large modules
with a finite product. This proves preservation of limits without
shrinking or replacing their carriers.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u v w

variable (R V : Type u) [CommRing R] [AddCommGroup V] [Module R V]

def tensor : ModuleCat.{u + 2} R ⥤ ModuleCat.{u + 2} R where
  obj M := ModuleCat.of R (M ⊗[R] V)
  map f := ModuleCat.ofHom (TensorProduct.map f.hom LinearMap.id)
  map_id _ := ModuleCat.hom_ext (by ext m v; rfl)
  map_comp _ _ := ModuleCat.hom_ext (by ext m v; rfl)

variable (ξ : Type u) [Fintype ξ] (b : Module.Basis ξ R V)

def power : ModuleCat.{u + 2} R ⥤ ModuleCat.{u + 2} R := Functor.const (Discrete ξ) ⋙ lim

def coordinate (M : ModuleCat.{u + 2} R) (i : ξ) : (tensor R V).obj M ⟶ M :=
  ModuleCat.ofHom ((LinearMap.proj i).comp (FiniteTensorCoordinates.LargeFiniteTensorCoordinates.equiv R ξ V b M).toLinearMap)

def cone (M : ModuleCat.{u + 2} R) : Cone ((Functor.const (Discrete ξ)).obj M) where
  pt := (tensor R V).obj M
  π :=
    { app i := coordinate R V ξ b M i.as
      naturality := by
        intro i j f
        have h : i = j := Discrete.ext (Discrete.eq_of_hom f)
        subst j
        simp }

def coneIsLimit (M : ModuleCat.{u + 2} R) : IsLimit (cone R V ξ b M) where
  lift s := ModuleCat.ofHom ((FiniteTensorCoordinates.LargeFiniteTensorCoordinates.equiv R ξ V b M).symm.toLinearMap.comp
    (LinearMap.pi (fun i => (s.π.app ⟨i⟩).hom)))
  fac s i := by
    apply ModuleCat.hom_ext
    ext x
    exact congrFun ((FiniteTensorCoordinates.LargeFiniteTensorCoordinates.equiv R ξ V b M).apply_symm_apply
      (fun i => s.π.app ⟨i⟩ x)) i.as
  uniq s m hm := by
    apply ModuleCat.hom_ext
    ext x
    apply (FiniteTensorCoordinates.LargeFiniteTensorCoordinates.equiv R ξ V b M).injective
    funext i
    exact (congrArg (fun f => f x) (hm ⟨i⟩)).trans
      (congrFun ((FiniteTensorCoordinates.LargeFiniteTensorCoordinates.equiv R ξ V b M).apply_symm_apply
        (fun j => s.π.app ⟨j⟩ x)) i).symm

def componentIso (M : ModuleCat.{u + 2} R) : (tensor R V).obj M ≅ (power R ξ).obj M :=
  (coneIsLimit R V ξ b M).conePointUniqueUpToIso (limit.isLimit _)

theorem component_pi (M : ModuleCat.{u + 2} R) (i : Discrete ξ) :
    (componentIso R V ξ b M).hom ≫ limit.π ((Functor.const (Discrete ξ)).obj M) i =
      coordinate R V ξ b M i.as :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ i

theorem coordinate_naturality {M N : ModuleCat.{u + 2} R} (f : M ⟶ N) (i : ξ) :
    (tensor R V).map f ≫ coordinate R V ξ b N i = coordinate R V ξ b M i ≫ f := by
  apply ModuleCat.hom_ext
  ext x
  exact congrFun (LinearMap.congr_fun (FiniteTensorCoordinates.LargeFiniteTensorCoordinates.naturality R ξ V b M N f.hom) x) i

def functorIso : tensor R V ≅ power R ξ :=
  NatIso.ofComponents (componentIso R V ξ b) (by
    intro M N f
    apply limit.hom_ext
    intro i
    have hl := limMap_π ((Functor.const (Discrete ξ)).map f) i
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun g => (tensor R V).map f ≫ g) (component_pi R V ξ b N i)).trans
        ((coordinate_naturality R V ξ b f i.as).trans
          ((congrArg (fun g => g ≫ f) (component_pi R V ξ b M i)).symm.trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun g => (componentIso R V ξ b M).hom ≫ g) hl).symm.trans
                (Category.assoc _ _ _).symm))))))

instance power_preservesLimits : PreservesLimitsOfSize.{w, v} (power R ξ) := by
  unfold power
  infer_instance

include b in
theorem tensor_preservesLimits : PreservesLimitsOfSize.{w, v} (tensor R V) :=
  preservesLimits_of_natIso (functorIso R V ξ b).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.FiniteFreeTensor.LargeFiniteFreeTensor

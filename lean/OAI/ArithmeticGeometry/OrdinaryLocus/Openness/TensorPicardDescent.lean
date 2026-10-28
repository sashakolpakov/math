import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FlatBaseChangeFunctions
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.RelativeBaseChange

/-! # Tensor Picard Descent -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorPicardDescent.Construction

noncomputable section

/-! Products over a field preserve Picard descent for a quasi-compact quasi-separated map preserving functions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory

variable {K : Type} [Field K]

theorem isPullback_tensor_left {A B : Over (Spec (.of K))} (f : A ⟶ B) (T : Over (Spec (.of K))) :
    IsPullback (fst A T).left (f ⊗ₘ 𝟙 T).left f.left (fst B T).left := by
  exact RelativeBaseChange.Construction.isPullback_overPullback_map f T.hom

theorem isPullback_tensor_right {A B : Over (Spec (.of K))} (f : A ⟶ B) (T : Over (Spec (.of K))) :
    IsPullback (snd T A).left (𝟙 T ⊗ₘ f).left f.left (snd T B).left := by
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback T.hom B.hom).flip
  · have he : (𝟙 T ⊗ₘ f).left ≫ (fst T B).left = (fst T A).left :=
      congrArg Over.Hom.left ((tensorHom_fst (𝟙 T) f).trans (Category.comp_id _))
    rw [Over.w f]
    change IsPullback (snd T A).left ((𝟙 T ⊗ₘ f).left ≫ (fst T B).left) A.hom T.hom
    rw [he]
    exact (IsPullback.of_hasPullback T.hom A.hom).flip
  · exact (congrArg Over.Hom.left (tensorHom_snd (𝟙 T) f)).symm

theorem tensor_left_preserves_functions
    {A B : Over (Spec (.of K))} (f : A ⟶ B) [QuasiCompact f.left] [QuasiSeparated f.left]
    (hf : ∀ U : B.left.Opens, IsIso (f.left.app U)) (T : Over (Spec (.of K)))
    (U : (B ⊗ T).left.Opens) : IsIso ((f ⊗ₘ 𝟙 T).left.app U) := by
  have : Flat (fst B T).left := inferInstanceAs (Flat (pullback.fst B.hom T.hom))
  exact FlatBaseChangeFunctions.Construction.isIso_app_flat_baseChange f.left (fst B T).left (fst A T).left (f ⊗ₘ 𝟙 T).left
    (isPullback_tensor_left f T) hf U

theorem tensor_right_preserves_functions
    {A B : Over (Spec (.of K))} (f : A ⟶ B) [QuasiCompact f.left] [QuasiSeparated f.left]
    (hf : ∀ U : B.left.Opens, IsIso (f.left.app U)) (T : Over (Spec (.of K)))
    (U : (T ⊗ B).left.Opens) : IsIso ((𝟙 T ⊗ₘ f).left.app U) := by
  have : Flat (snd T B).left := inferInstanceAs (Flat (pullback.snd T.hom B.hom))
  exact FlatBaseChangeFunctions.Construction.isIso_app_flat_baseChange f.left (snd T B).left (snd T A).left (𝟙 T ⊗ₘ f).left
    (isPullback_tensor_right f T) hf U

theorem picardPullback_tensor_left_injective
    {A B : Over (Spec (.of K))} (f : A ⟶ B) [QuasiCompact f.left] [QuasiSeparated f.left]
    (hf : ∀ U : B.left.Opens, IsIso (f.left.app U)) (T : Over (Spec (.of K))) :
    Function.Injective (PicardPullback.Construction.picardPullback (f ⊗ₘ 𝟙 T).left) :=
  PicardPullback.Construction.picardPullback_injective_of_app _ (tensor_left_preserves_functions f hf T)

theorem picardPullback_tensor_right_injective
    {A B : Over (Spec (.of K))} (f : A ⟶ B) [QuasiCompact f.left] [QuasiSeparated f.left]
    (hf : ∀ U : B.left.Opens, IsIso (f.left.app U)) (T : Over (Spec (.of K))) :
    Function.Injective (PicardPullback.Construction.picardPullback (𝟙 T ⊗ₘ f).left) :=
  PicardPullback.Construction.picardPullback_injective_of_app _ (tensor_right_preserves_functions f hf T)

theorem tensor_product_preserves_functions
    {A B C D : Over (Spec (.of K))} (f : A ⟶ B) (g : C ⟶ D)
    [QuasiCompact f.left] [QuasiSeparated f.left] [QuasiCompact g.left] [QuasiSeparated g.left]
    (hf : ∀ U : B.left.Opens, IsIso (f.left.app U))
    (hg : ∀ U : D.left.Opens, IsIso (g.left.app U)) (U : (B ⊗ D).left.Opens) :
    IsIso ((f ⊗ₘ g).left.app U) := by
  have h : (f ⊗ₘ 𝟙 C) ≫ (𝟙 B ⊗ₘ g) = f ⊗ₘ g := tensor_id_comp_id_tensor g f
  have : IsIso ((𝟙 B ⊗ₘ g).left.app U) := tensor_right_preserves_functions g hg B U
  have : IsIso ((f ⊗ₘ 𝟙 C).left.app ((𝟙 B ⊗ₘ g).left ⁻¹ᵁ U)) :=
    tensor_left_preserves_functions f hf C _
  have hi : IsIso (((f ⊗ₘ 𝟙 C).left ≫ (𝟙 B ⊗ₘ g).left).app U) := by
    exact (asIso ((𝟙 B ⊗ₘ g).left.app U) ≪≫
      asIso ((f ⊗ₘ 𝟙 C).left.app ((𝟙 B ⊗ₘ g).left ⁻¹ᵁ U))).isIso_hom
  exact (congrArg (fun h => IsIso (h.left.app U)) h) ▸ hi

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorPicardDescent.Construction

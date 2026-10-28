import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupRigidity
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperFunctionsEq
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Proper Group Functions -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.ProperGroupFunctions

noncomputable section

/-! Global functions on the product of a proper connected smooth group
with an arbitrary affine scheme come from the affine factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {k : Type u} [Field k]
variable (A : Over (Spec (.of k))) [GrpObj A] [Smooth A.hom]
variable [IsProper A.hom] [GeometricallyConnected A.hom]

theorem properGroup_appTop_isIso : IsIso A.hom.appTop := by
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace_of_subsingleton A.hom
  have : IsReduced A.left := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field A.hom
  exact Quotients.FiniteDescent.ProperFunctionsEq.Construction.ProperFunctions.isIso_appTop_of_section A η[A].left (Over.w η[A])

theorem properGroupProduct_appTop_isIso
    (T : Over (Spec (.of k))) [IsAffine T.left] : IsIso (fst T A).left.appTop := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsNoetherian A.left := ⟨⟩
  have : QuasiSeparatedSpace A.left := inferInstance
  let H := (IsPullback.of_hasPullback T.hom A.hom).flip
  have hA : (⊤ : A.left.Opens) ≤ A.hom ⁻¹ᵁ ⊤ := le_rfl
  have hT : (⊤ : T.left.Opens) ≤ T.hom ⁻¹ᵁ ⊤ := le_rfl
  have hP : (fst T A).left ⁻¹ᵁ ⊤ =
      (snd T A).left ⁻¹ᵁ ⊤ ⊓ (fst T A).left ⁻¹ᵁ ⊤ := by simp
  have hq := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hT hA hP
    (isAffineOpen_top (Spec (.of k))) (isAffineOpen_top T.left)
    isCompact_univ isQuasiSeparated_univ
  have hp := (isIso_pushoutSection_iff H hT hA hP).mp hq
  have : IsIso (A.hom.appLE ⊤ ⊤ hA) := by
    change IsIso (A.hom.appLE ⊤ (A.hom ⁻¹ᵁ ⊤) le_rfl)
    rw [Scheme.Hom.appLE_eq_app]
    exact properGroup_appTop_isIso A
  have h := hp.isIso_inr_of_isIso
  change IsIso ((fst T A).left.appLE ⊤ ((fst T A).left ⁻¹ᵁ ⊤) le_rfl) at h
  rw [Scheme.Hom.appLE_eq_app] at h
  exact h

def properGroupProductFunctionsEquiv
    (T : Over (Spec (.of k))) [IsAffine T.left] :
    Γ(T.left, ⊤) ≃+* Γ((T ⊗ A).left, ⊤) := by
  have := properGroupProduct_appTop_isIso A T
  exact (asIso (fst T A).left.appTop).commRingCatIsoToRingEquiv

theorem properGroupProduct_affine_target
    (T Z : Over (Spec (.of k))) [IsAffine T.left] [IsAffine Z.left]
    (f : T ⊗ A ⟶ Z) :
    f = fst T A ≫ lift (𝟙 T) (toUnit T ≫ η[A]) ≫ f := by
  let p := fst T A
  let s : T ⟶ T ⊗ A := lift (𝟙 T) (toUnit T ≫ η[A])
  have hs : s ≫ p = 𝟙 T := lift_fst _ _
  have : IsIso p.left.appTop := properGroupProduct_appTop_isIso A T
  have he : p.left.appTop ≫ s.left.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, hs, Over.id_left, Scheme.Hom.id_appTop]
  have he' : s.left.appTop ≫ p.left.appTop = 𝟙 _ := by
    apply (cancel_epi p.left.appTop).mp
    rw [← Category.assoc, he, Category.id_comp, Category.comp_id]
  apply Over.OverMorphism.ext
  apply AlgebraicGeometry.ext_of_isAffine
  change f.left.appTop = (p.left ≫ s.left ≫ f.left).appTop
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Category.assoc, he', Category.comp_id]

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.ProperGroupFunctions

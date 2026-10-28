import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Global Functions -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.GlobalFunctions.Construction

noncomputable section

/-!
# Completion: global functions on a proper integral geometric scheme

Over an algebraically closed field the structure map induces an isomorphism
on global sections. Consequently every map to an affine scheme is constant
along this proper integral scheme, with its value determined by any section.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [UniversallyClosed p]

/-- An integral proper geometric scheme has only constant global regular functions. -/
theorem properIntegral_appTop_isIso : IsIso p.appTop := by
  let f : CommRingCat.of K ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso _).inv ≫ p.appTop
  have hf : f.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  have : IsIso f := (ConcreteCategory.isIso_iff_bijective f).mpr
    (IsAlgClosed.ringHom_bijective_of_isIntegral f.hom hf)
  exact (isIso_comp_left_iff (Scheme.ΓSpecIso _).inv p.appTop).mp this

/-- The value at a section determines every morphism to an affine target. -/
theorem properIntegral_to_affine_constant {Z : Scheme.{u}} [IsAffine Z]
    (e : Spec (CommRingCat.of K) ⟶ X) (he : e ≫ p = 𝟙 _) (f : X ⟶ Z) :
    f = p ≫ e ≫ f := by
  have : IsIso p.appTop := properIntegral_appTop_isIso p
  have h : p.appTop ≫ e.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
  have h' : e.appTop ≫ p.appTop = 𝟙 _ := by
    rw [← cancel_epi p.appTop, ← Category.assoc, h]
    simp
  apply ext_of_isAffine
  simp only [Scheme.Hom.comp_appTop, ← Category.assoc, h', Category.comp_id]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.GlobalFunctions.Construction

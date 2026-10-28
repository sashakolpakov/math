import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.AffineFieldBaseChange
import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralGenericFiniteness
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.UnramifiedSections
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Normal Base Proper Finiteness -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalBaseProperFiniteness.Construction

noncomputable section

/-!
# Completion: finiteness of proper global functions over a normal affine base

The actual generic global functions are finite. Formal unramifiedness
makes their field extension separable; the trace bound then proves
finiteness of the original integral global function algebra.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- The actual proper global section map is finite under the proved unramifiedness condition. -/
theorem normal_base_proper_appTop_finite (R : Type u) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [IsDominant f]
    [IsDomain Γ(X, ⊤)] [FormallyUnramified f.fromNormalization] : f.appTop.hom.Finite := by
  let F : CommRingCat.of R ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso _).inv ≫ f.appTop
  have hI : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  have hU : F.hom.FormallyUnramified :=
    (RingHom.FormallyUnramified.of_surjective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective).comp
      (Proper.UnramifiedSections.Construction.proper_appTop_formallyUnramified f)
  have : IsSchemeTheoreticallyDominant f := .of_isDominant f
  have hj : Function.Injective F :=
    (show Function.Injective f.appTop from by simpa [Scheme.Hom.appTop] using f.app_injective ⊤).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).injective
  algebraize [F.hom]
  have : Algebra.IsIntegral R Γ(X, ⊤) := ⟨hI⟩
  have : Algebra.FormallyUnramified R Γ(X, ⊤) := hU
  have : FaithfulSMul R Γ(X, ⊤) := (faithfulSMul_iff_algebraMap_injective R Γ(X, ⊤)).mpr hj
  have : Module.Finite (FractionRing R) (FractionRing R ⊗[R] Γ(X, ⊤)) :=
    Proper.AffineFieldBaseChange.Construction.proper_fraction_globalFunctionDomain_finite R (FractionRing R) f rfl
  have hF : F.hom.Finite := IntegralGenericFiniteness.Construction.integral_unramified_finite_of_generic_finite R (FractionRing R) Γ(X, ⊤)
  have he : f.appTop = (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ F := by simp [F]
  rw [he, CommRingCat.hom_comp]
  exact hF.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).surjective)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalBaseProperFiniteness.Construction

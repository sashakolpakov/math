import Mathlib.AlgebraicGeometry.Restrict

/-! # Lift Section Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.LiftSectionMap

noncomputable section

/-! The global-section map of a genuine lift into an open is the
original scheme's restriction-aware section map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem openLift_sectionMap {X Y : Scheme.{0}} (U : Y.Opens)
    (p : X ⟶ U.toScheme) (f : X ⟶ Y) (h : p ≫ U.ι = f)
    (hf : (⊤ : X.Opens) ≤ f ⁻¹ᵁ U) (s : Γ(Y, U)) :
    p.appTop (U.topIso.inv s) = f.appLE U ⊤ hf s := by
  subst f
  have hi : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    exact congrArg Y.presheaf.map (Subsingleton.elim _ _)
  have hp : p.appLE ⊤ ⊤ (by intro x _; trivial) = p.appTop := p.appLE_eq_app
  have hc := Scheme.Hom.appLE_comp_appLE p U.ι U ⊤ ⊤ U.ι_preimage_self.ge (by intro x _; trivial)
  rw [hi, hp] at hc
  exact ConcreteCategory.congr_hom hc s

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.LiftSectionMap

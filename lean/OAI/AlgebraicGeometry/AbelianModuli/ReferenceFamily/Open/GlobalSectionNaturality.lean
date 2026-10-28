import Mathlib.AlgebraicGeometry.Restrict

/-! # Global Section Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.GlobalSectionNaturality

noncomputable section

/-! Global sections restricted to an open use the original
ambient restriction map after the canonical top-section identification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem openTopSection_global {X : Scheme.{0}} (U : X.Opens) (s : Γ(X, ⊤)) :
    U.topIso.hom (U.ι.appTop s) = X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s := by
  have h : U.ι.appTop ≫ U.topIso.hom = X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
    exact (X.presheaf.map_comp _ _).symm.trans (congrArg X.presheaf.map (Subsingleton.elim _ _))
  exact ConcreteCategory.congr_hom h s

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.GlobalSectionNaturality

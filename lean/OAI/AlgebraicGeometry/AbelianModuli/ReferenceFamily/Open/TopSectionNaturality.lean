import Mathlib.AlgebraicGeometry.Restrict

/-! # Top Section Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.TopSectionNaturality

noncomputable section

/-! The original top-section isomorphisms commute with inclusions
of open subschemes and the actual ambient restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem openTopSection_restrict {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U)
    (s : Γ(U.toScheme, ⊤)) :
    V.topIso.hom ((X.homOfLE h).appTop s) =
      X.presheaf.map (homOfLE h).op (U.topIso.hom s) := by
  have e : (X.homOfLE h).appTop ≫ V.topIso.hom =
      U.topIso.hom ≫ X.presheaf.map (homOfLE h).op := by
    rw [Scheme.homOfLE_appTop]
    simp only [Scheme.Opens.topIso_hom]
    exact (X.presheaf.map_comp _ _).symm.trans
      ((congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _))
  exact ConcreteCategory.congr_hom e s

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.TopSectionNaturality

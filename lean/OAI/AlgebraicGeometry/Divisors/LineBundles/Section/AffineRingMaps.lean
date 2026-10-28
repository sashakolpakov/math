import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.OpenRestriction
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Affine Ring Maps -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Section.AffineRingMaps.BundleCycles

noncomputable section

/-! The rings of compatible affine section neighborhoods retain the
actual section retraction and its kernel ideal, without chart choices. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (p : Y ⟶ X) (s : X ⟶ Y) (hs : s ≫ p = 𝟙 X)
    (U : Y.Opens) (V : X.Opens) (hV : V ≤ s ⁻¹ᵁ U) (hU : U ≤ p ⁻¹ᵁ V)

include hs in
theorem section_appLE_retraction :
    p.appLE V U hU ≫ s.appLE U V hV = 𝟙 Γ(X, V) := by
  rw [Scheme.Hom.appLE_comp_appLE]
  have h : ∀ (f : X ⟶ X) (hf : f = 𝟙 X) (e : V ≤ f ⁻¹ᵁ V),
      f.appLE V V e = 𝟙 Γ(X, V) := by
    intro f hf e
    subst f
    change 𝟙 Γ(X, V) ≫ X.presheaf.map (𝟙 (Opposite.op V)) = 𝟙 Γ(X, V)
    rw [X.presheaf.map_id, Category.id_comp]
  exact h _ hs _

include hs hU in
theorem section_appLE_kernel [IsClosedImmersion s] (hUaff : IsAffineOpen U) :
    RingHom.ker (s.appLE U V hV).hom = s.ker.ideal ⟨U, hUaff⟩ := by
  have he : s ⁻¹ᵁ U = V := OpenRestriction.BundleCycles.sectionOpen_preimage p s hs U V hV hU
  have hm : IsIso (X.presheaf.map (homOfLE hV).op) := by
    have : IsIso (homOfLE hV) := by
      change IsIso (eqToHom he.symm)
      infer_instance
    infer_instance
  have hi : Function.Injective (X.presheaf.map (homOfLE hV).op).hom :=
    (ConcreteCategory.bijective_of_isIso (X.presheaf.map (homOfLE hV).op)).injective
  rw [Scheme.Hom.ker_apply]
  change RingHom.ker ((X.presheaf.map (homOfLE hV).op).hom.comp (s.app U).hom) = _
  exact RingHom.ker_comp_of_injective _ hi

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Section.AffineRingMaps.BundleCycles

import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict

/-! # Range Section Pullback -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Open.RangeSectionPullback.Constructions.Sections

/-! Global sections on an open immersion's source give actual global
sections of its literal open range, with the native germ compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]

theorem gammaIsoTop_inv : (IsOpenImmersion.ΓIsoTop f).inv =
    f.appLE f.opensRange ⊤ (by rw [f.preimage_opensRange]) := by
  simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv,
    eqToIso.inv, eqToHom_op, Iso.symm_inv, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

def rangeSection (s : Γ(X, ⊤)) : Γ(f.opensRange.toScheme, ⊤) :=
  f.opensRange.topIso.inv ((IsOpenImmersion.ΓIsoTop f).hom s)

theorem rangeSection_topIso (s : Γ(X, ⊤)) :
    f.opensRange.topIso.hom (rangeSection f s) = (IsOpenImmersion.ΓIsoTop f).hom s :=
  Iso.inv_hom_id_apply _ _

theorem rangeSection_germ (x : X) (s : Γ(X, ⊤)) :
    f.stalkMap x (Y.presheaf.germ f.opensRange (f x) ⟨x, rfl⟩
      (f.opensRange.topIso.hom (rangeSection f s))) = X.presheaf.germ ⊤ x trivial s := by
  rw [rangeSection_topIso]
  have h : f.appLE f.opensRange ⊤ (by rw [f.preimage_opensRange]) ≫ X.presheaf.germ ⊤ x trivial =
      Y.presheaf.germ f.opensRange (f x) ⟨x, rfl⟩ ≫ f.stalkMap x := by
    rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res, f.germ_stalkMap]
  have he := ConcreteCategory.congr_hom h ((IsOpenImmersion.ΓIsoTop f).hom s)
  rw [← gammaIsoTop_inv] at he
  simpa only [CommRingCat.comp_apply, Iso.hom_inv_id_apply] using he.symm

end AlgebraicGeometry.CycleClass.Thom.Open.RangeSectionPullback.Constructions.Sections

namespace AlgebraicGeometry.CycleClass.Thom.Open.RangeSectionPullback.Constructions

/-! Pullback through the actual isomorphism onto an open immersion's
range recovers the original global sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.RangeSectionPullback.Constructions.Sections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]

theorem rangeIso_appTop : f.opensRange.topIso.inv ≫ f.isoOpensRange.hom.appTop = (IsOpenImmersion.ΓIsoTop f).inv := by
  have ht : f.opensRange.topIso.inv = f.opensRange.ι.appLE f.opensRange ⊤ f.opensRange.ι_preimage_self.ge := by
    simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
    rfl
  have hk : f.isoOpensRange.hom.appTop = f.isoOpensRange.hom.appLE ⊤ ⊤ (by rw [Scheme.Hom.preimage_top]) := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  rw [ht, hk, Scheme.Hom.appLE_comp_appLE]
  simp only [Scheme.Hom.isoOpensRange_hom_ι, Sections.gammaIsoTop_inv]

theorem rangeSection_pullback (s : Γ(X, ⊤)) : f.isoOpensRange.hom.appTop (Sections.rangeSection f s) = s := by
  have h := ConcreteCategory.congr_hom (rangeIso_appTop f) ((IsOpenImmersion.ΓIsoTop f).hom s)
  exact h.trans (Iso.hom_inv_id_apply _ s)

end AlgebraicGeometry.CycleClass.Thom.Open.RangeSectionPullback.Constructions

end

end OAI

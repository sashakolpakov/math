import OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothLocalDomains
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth Stalk Domains -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothStalkDomains.Construction

noncomputable section

/-!
# Completion: domain stalks of actual smooth schemes over fields

Affine sections of the structural morphism are smooth algebras. Their
prime localizations identify with the actual scheme stalks.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f]

include K f

/-- Every stalk of a smooth scheme over a field is an integral domain. -/
theorem smooth_field_stalk_isDomain (x : X) : IsDomain (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let := ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  have hs := f.smooth_appLE (isAffineOpen_top _) hU (by simp)
  algebraize [(f.appLE ⊤ U (by simp)).hom]
  have : Algebra.Smooth Γ(Spec (CommRingCat.of K), ⊤) Γ(X, U) := hs
  let p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  have : IsDomain (Localization.AtPrime p) :=
    SmoothLocalDomains.Construction.smooth_field_localization_isDomain Γ(Spec (CommRingCat.of K), ⊤) Γ(X, U) p
  algebraize [(X.presheaf.germ U x hxU).hom]
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk x)
    (Localization.AtPrime p)).toRingEquiv.toMulEquiv.isDomain _

theorem smooth_field_affine_sections_isIntegrallyClosed (U : X.Opens)
    (hU : IsAffineOpen U) [IsDomain Γ(X, U)] : IsIntegrallyClosed Γ(X, U) := by
  let := ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  have hs := f.smooth_appLE (isAffineOpen_top _) hU (by simp)
  algebraize [(f.appLE ⊤ U (by simp)).hom]
  have : Algebra.Smooth Γ(Spec (CommRingCat.of K), ⊤) Γ(X, U) := hs
  exact SmoothLocalDomains.Construction.smooth_field_domain_isIntegrallyClosed Γ(Spec (CommRingCat.of K), ⊤) Γ(X, U)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothStalkDomains.Construction

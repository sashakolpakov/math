import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Basic

/-! # Field Base Stalk -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.FieldBaseStalk.Constructions

noncomputable section

/-! On the spectrum of a field, the actual germ of global sections is
an isomorphism, proved from the native affine-stalk localization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem fieldBase_germ_isIso (K : Type) [Field K] (x : Spec (CommRingCat.of K)) :
    IsIso ((Spec (CommRingCat.of K)).presheaf.germ ⊤ x (by trivial)) := by
  let X := Spec (CommRingCat.of K)
  let z : (⊤ : X.Opens) := ⟨x, by trivial⟩
  let := X.presheaf.algebra_section_stalk z
  let P := (isAffineOpen_top X).primeIdealOf z
  let : IsLocalization.AtPrime (X.presheaf.stalk x) P.asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk z
  let e : Γ(X, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have hU : P.asIdeal.primeCompl ≤ IsUnit.submonoid Γ(X, ⊤) := by
    intro a ha
    have ha0 : a ≠ 0 := by
      intro h
      exact ha (h ▸ P.asIdeal.zero_mem)
    have he0 : e a ≠ 0 := by
      intro h
      exact ha0 (e.injective (h.trans e.map_zero.symm))
    have hu := (isUnit_iff_ne_zero.mpr he0).map e.symm.toRingHom
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at hu
    exact hu
  let l := IsLocalization.atUnits Γ(X, ⊤) P.asIdeal.primeCompl (S := X.presheaf.stalk x) hU
  exact (ConcreteCategory.isIso_iff_bijective _).mpr l.bijective

end

end OAI.AlgebraicGeometry.CycleClass.Thom.FieldBaseStalk.Constructions

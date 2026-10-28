import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Nilpotent Affine Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentAffineSections

noncomputable section

/-! Global nilpotence of a closed-immersion ideal gives nilpotence
of every genuine affine section reduction kernel. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] (hi : IsNilpotent i.ker)

include hi in
theorem app (U : Y.Opens) (hU : IsAffineOpen U) : IsNilpotent (RingHom.ker (i.app U).hom) := by
  obtain ⟨N, hN⟩ := hi
  refine ⟨N, ?_⟩
  simpa using congrArg (fun I : Y.IdealSheafData => I.ideal ⟨U, hU⟩) hN

include hi in
theorem appTop [IsAffine Y] : IsNilpotent (RingHom.ker i.appTop.hom) := by
  simpa [Scheme.Hom.appTop] using NilpotentAffineSections.app i hi ⊤ (isAffineOpen_top Y)

/-- On an affine target, the native global section kernel detects
nilpotence of the actual closed-immersion ideal sheaf. -/
theorem of_appTop [IsAffine Y] (h : IsNilpotent (RingHom.ker i.appTop.hom)) :
    IsNilpotent i.ker := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  simpa [Scheme.Hom.appTop] using hN

theorem spec {R S : CommRingCat.{u}} (ρ : R ⟶ S)
    [IsClosedImmersion (Spec.map ρ)] (hρ : IsNilpotent (RingHom.ker ρ.hom)) :
    IsNilpotent (Spec.map ρ).ker := by
  apply of_appTop
  have hk : RingHom.ker (Spec.map ρ).appTop.hom =
      (RingHom.ker ρ.hom).comap (Scheme.ΓSpecIso R).hom.hom := by
    rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv,
      RingHom.comap_ker, RingEquiv.toRingHom_eq_coe,
      Iso.commRingCatIsoToRingEquiv_toRingHom, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality]
  obtain ⟨N, hN⟩ := hρ
  refine ⟨N, le_antisymm ?_ bot_le⟩
  rw [hk]
  refine (Ideal.le_comap_pow (Scheme.ΓSpecIso R).hom.hom N).trans ?_
  rw [hN]
  intro r hr
  apply (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.injective
  change (Scheme.ΓSpecIso R).hom r = (Scheme.ΓSpecIso R).hom 0
  simpa using hr

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentAffineSections

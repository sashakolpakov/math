import OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialTransform

/-! # Kernel Order Equiv -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelOrderEquiv.Construction

noncomputable section

/-! Every native affine ideal has an exact algebraic kernel representative, with reflected inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_affineQuotientKernel {R : Type u} [CommRing R]
    (J : (Spec (.of R)).IdealSheafData) : ∃ I : Ideal R, QuotientKernel.Construction.affineQuotientKernel I = J := by
  let U : (Spec (.of R)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let e := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  refine ⟨(J.ideal U).map e.toRingHom, ?_⟩
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [QuotientKernel.Construction.affineQuotientKernel_idealTop]
  exact Ideal.comap_map_of_bijective e.toRingHom e.bijective

theorem affineQuotientKernel_le_iff {R : Type u} [CommRing R] (I J : Ideal R) :
    QuotientKernel.Construction.affineQuotientKernel I ≤ QuotientKernel.Construction.affineQuotientKernel J ↔ I ≤ J := by
  constructor
  · intro h
    have he := h ⟨⊤, isAffineOpen_top (Spec (.of R))⟩
    rw [QuotientKernel.Construction.affineQuotientKernel_idealTop, QuotientKernel.Construction.affineQuotientKernel_idealTop] at he
    have hm := Ideal.map_mono (f := (Scheme.ΓSpecIso (.of R)).hom.hom) he
    simpa only [Ideal.map_comap_of_surjective (Scheme.ΓSpecIso (.of R)).hom.hom
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.surjective] using hm
  · exact Global.DifferentialTransform.Construction.affineQuotientKernel_mono

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelOrderEquiv.Construction

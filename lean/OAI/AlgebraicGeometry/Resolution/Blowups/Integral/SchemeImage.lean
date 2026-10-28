import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedTransformProjectivity
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Scheme Image -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Integral.SchemeImage.Construction

noncomputable section

/-! The actual scheme-theoretic image of an integral source is integral. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem scheme_image_isReduced
    {Z Y : Scheme.{u}} (f : Z ⟶ Y) [QuasiCompact f] [IsReduced Z] : IsReduced f.image := by
  have hred (U : Y.affineOpens) : IsReduced (Spec (.of (Γ(Y, U) ⧸ f.ker.ideal U))) := by
    have hrad : (f.ker.ideal U).IsRadical := by
      rw [Scheme.Hom.ker_apply]
      intro a ha
      obtain ⟨n, hn⟩ := ha
      change (f.app U.1).hom a = 0
      apply IsNilpotent.eq_zero
      refine ⟨n, ?_⟩
      change (f.app U.1).hom (a ^ n) = 0 at hn
      rwa [map_pow] at hn
    let : _root_.IsReduced (Γ(Y, U) ⧸ f.ker.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced (f.ker.ideal U)).mp hrad
    infer_instance
  let : ∀ U : f.ker.subschemeCover.openCover.I₀, IsReduced (f.ker.subschemeCover.openCover.X U) :=
    fun U => hred U
  exact IsReduced.of_openCover f.image f.ker.subschemeCover.openCover

theorem scheme_image_isIntegral
    {Z Y : Scheme.{u}} (f : Z ⟶ Y) [QuasiCompact f] [IsIntegral Z] : IsIntegral f.image := by
  let : IsReduced f.image := scheme_image_isReduced f
  have hr : IsIrreducible (Set.range f.toImage) := by
    simpa only [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ Z).image
      f.toImage f.toImage.continuous.continuousOn
  have hwhole : IsIrreducible (Set.univ : Set f.image) := f.toImage.denseRange.closure_eq ▸ hr.closure
  let : IrreducibleSpace f.image := (irreducibleSpace_def f.image).mpr hwhole
  exact isIntegral_of_irreducibleSpace_of_isReduced f.image

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Integral.SchemeImage.Construction

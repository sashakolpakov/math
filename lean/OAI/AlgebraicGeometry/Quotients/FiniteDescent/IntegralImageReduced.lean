import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ReducedClosedIs

/-! # Integral Image Reduced -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.IntegralImageReduced.Construction.IntegralImage

/-! Scheme-theoretic images of quasi-compact maps from integral schemes are integral. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem reduced {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X] [QuasiCompact f] :
    IsReduced f.image := by
  have hred (U : Y.affineOpens) : _root_.IsReduced (Γ(Y, U) ⧸ f.ker.ideal U) := by
    apply (Ideal.isRadical_iff_quotient_reduced _).mp
    rw [f.ker_apply U, RingHom.ker_eq_comap_bot]
    exact Ideal.isRadical_bot.comap _
  have (U : f.ker.subschemeCover.openCover.I₀) :
      IsReduced (f.ker.subschemeCover.openCover.X U) := by
    have := hred U
    change IsReduced (Spec (.of (Γ(Y, U.1) ⧸ f.ker.ideal U)))
    infer_instance
  exact IsReduced.of_openCover f.image f.ker.subschemeCover.openCover

theorem irreducible {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X] [QuasiCompact f] :
    IrreducibleSpace f.image := by
  have hr : IsIrreducible (Set.range f.toImage) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ X).image f.toImage f.toImage.continuous.continuousOn
  have hc : IsIrreducible (Set.univ : Set f.image) := by
    rw [← f.toImage.denseRange.closure_eq]
    exact hr.closure
  exact (irreducibleSpace_def f.image).mpr hc

theorem integral {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [QuasiCompact f] :
    IsIntegral f.image := by
  have := reduced f
  have := irreducible f
  exact isIntegral_of_irreducibleSpace_of_isReduced f.image

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.IntegralImageReduced.Construction.IntegralImage

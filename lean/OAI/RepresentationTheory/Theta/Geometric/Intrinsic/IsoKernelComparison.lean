import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodProjectionNaturality

/-! # Iso Kernel Comparison -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.IsoKernelComparison

noncomputable section

/-! An actual algebraic group isomorphism identifies both original
native period kernels through its genuine rational period map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodProjectionNaturality.IntrinsicLinearMaps

theorem nativeIso_period_kernel_iff {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (e : A.toOver ≅ B.toOver) [IsMonHom e.hom]
    (u : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom).baseChange ℂ u ∈ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection B).ker ↔
      u ∈ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker := by
  constructor
  · intro hu
    have h := AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodProjectionNaturality.IntrinsicLinearMaps.rationalLift_isHodgeMap e.inv ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom).baseChange ℂ u) hu
    change (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.inv).baseChange ℂ ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom).baseChange ℂ u) ∈
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker at h
    simpa only [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp,
      Iso.hom_inv_id, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_id, LinearMap.baseChange_id, LinearMap.id_apply] using h
  · exact fun hu => AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodProjectionNaturality.IntrinsicLinearMaps.rationalLift_isHodgeMap e.hom u hu

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.IsoKernelComparison

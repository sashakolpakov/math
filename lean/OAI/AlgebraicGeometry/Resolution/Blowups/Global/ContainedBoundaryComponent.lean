import OAI.AlgebraicGeometry.Resolution.Blowups.ContainedBoundaryComponentCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedCenterPointedRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedCenterCoordinateChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedCenterSupportCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ChartSupport

/-! # Contained Boundary Component -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! A boundary component containing a native center can be adjoined to its full global atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.adjoin_boundary_component
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} [Fintype β] {D : β → X.IdealSheafData}
    (A : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (H : X.IdealSheafData) (hHI : H ≤ I)
    (B : MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f
      (fun j : Option β => match j with | none => H | some l => D l) [Finset.univ]) :
    CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I (fun j : Option β => match j with | none => H | some l => D l) := by
  classical
  let E : Option β → X.IdealSheafData := fun j => match j with | none => H | some l => D l
  apply CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofCenterCharts f I E B
  intro x hx
  obtain ⟨i, p, hp⟩ := MonomialBoundaryAtlas.Construction.exists_point_on_chosen_affine_spec B.opens B.cover x
  let U := B.opens i
  let : Algebra ℂ Γ(X, U) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have hI : I.comap U.2.fromSpec = Affine.QuotientKernel.Construction.affineQuotientKernel (I.ideal U) :=
    Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel I U
  have hw (l : β) : (D l).comap U.2.fromSpec = Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {B.equations i (some l)}) :=
    (Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel (D l) U).trans
      (congrArg Affine.QuotientKernel.Construction.affineQuotientKernel (B.component i (some l)))
  have hIp : I.ideal U ≤ p.asIdeal := by
    have hs := congrArg (fun K : (Spec (.of Γ(X, U))).IdealSheafData =>
      (K.support : Set (Spec (.of Γ(X, U))))) hI
    rw [Scheme.IdealSheafData.support_comap, Coefficient.ChartSupport.Construction.affineQuotientKernel_support] at hs
    change p ∈ PrimeSpectrum.zeroLocus (I.ideal U)
    rw [← hs]
    change U.2.fromSpec p ∈ I.support
    rw [hp]
    exact hx
  obtain ⟨F, C⟩ := A.exists_pointed_restriction (.of Γ(X, U)) U.2.fromSpec
    (Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U).symm (I.ideal U) (fun l => B.equations i (some l)) hI hw p hIp
  obtain ⟨C⟩ := C
  let : Algebra ℂ C.chart.carrier := C.chart.algebra
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom C.chart.map.toRingHom)) := C.chart.isOpenImmersion
  have hc : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts ℂ C.chart.carrier ((I.ideal U).map C.chart.map.toRingHom)
      (fun l => C.chart.map (B.equations i (some l))) F := by
    rw [C.center_eq]
    exact C.chart.model.hasMixedCenterCharts C.coordinates F C.divided_iff
  have hz : B.equations i none ∈ I.ideal U := by
    apply hHI U
    rw [B.component i none]
    exact Ideal.mem_span_singleton_self _
  have hf : C.chart.map.toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom C.chart.map.toRingHom)).mp inferInstance
  have hfull : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ C.chart.carrier
      (fun j : Option β => match j with
        | none => C.chart.map (B.equations i none)
        | some l => C.chart.map (B.equations i (some l))) := by
    convert (B.boundary i).etale_baseChange C.chart.map hf using 1
    funext j
    cases j <;> rfl
  have hcfull := hc.adjoin_boundary_component (C.chart.map (B.equations i none))
    (Ideal.mem_map_of_mem _ hz) hfull
  have hIC : (I.ideal U).map C.chart.map.toRingHom ≤ C.chart.point.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    exact hIp.trans_eq (congrArg PrimeSpectrum.asIdeal C.chart.point_over).symm
  obtain ⟨M⟩ := hcfull C.chart.point hIC
  have M' : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart ℂ C.chart.carrier
      ((I.ideal U).map C.chart.map.toRingHom) (fun l => C.chart.map (B.equations i l))
      (insert none (F.image some)) C.chart.point := by
    convert M using 1
    first | rfl | (funext j; cases j <;> rfl)
  let N := M'.comp (R := .of Γ(X, U)) (S := C.chart.carrier)
    (I.ideal U) (B.equations i) (insert none (F.image some)) C.chart.map p C.chart.point_over
  let V := MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart.ofNativeCoordinateChart f I E U (B.equations i)
    (B.component i) _ p N
  refine ⟨V, N.chart.point, ?_⟩
  exact (congrArg U.2.fromSpec N.chart.point_over).trans hp

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global

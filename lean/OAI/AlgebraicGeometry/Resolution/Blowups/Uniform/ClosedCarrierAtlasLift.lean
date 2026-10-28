import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.ClosedCarrierPointedLift
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CenterAtlasGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.IntrinsicNormalOpenRefinement
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedCenterSupportCharts

/-! # Closed Carrier Atlas Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A carrier center with a prescribed incidence set lifts to an ambient atlas with that same set. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.exists_uniform_liftClosedCarrierCenter
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I H : X.IdealSheafData) (hH : H ≠ ⊥)
    [Smooth (H.subschemeι ≫ f)] (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (hHI : H ≤ I)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) {L : List (Finset β)}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L)
    (B : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (H.subschemeι ≫ f) (I.comap H.subschemeι)
      (fun l => (D l).comap H.subschemeι)) (F : Finset β) (hF : ∀ i, B.divided i = F) :
    ∃ C : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D, ∀ i, C.divided i = F := by
  apply Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.exists_uniform_ofCenterCharts f I D A F
  intro x hx
  have hxH : x ∈ H.support := Scheme.IdealSheafData.support_antitone hHI hx
  have hxA : x ∈ ⨆ i, (A.opens i).1 := by rw [A.cover]; trivial
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxA
  obtain ⟨V, hxV, hVi, z, hHz, N, hNz⟩ :=
    IntrinsicNormalOpenRefinement.Construction.exists_native_normal_neighborhood_within f H hH hlocal (A.opens i).1 x hxH hxi
  let : Algebra ℂ Γ(X, V) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f V
  have hVU : V ≤ A.opens i := hVi
  let w (l : β) : Γ(X, V) := Blowup.Functor.Construction.affineRestriction hVU (A.equations i l)
  have hw (l : β) : (D l).ideal V = Ideal.span {w l} :=
    Locally.PrincipalIdealSheaf.Construction.principal_idealSheaf_restrict (D l) hVU (A.equations i l) (A.component i l)
  let : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
  have hxrange : x ∈ V.2.fromSpec.opensRange := by rw [V.2.opensRange_fromSpec]; exact hxV
  obtain ⟨p, hp⟩ := hxrange
  have hIp : I.ideal V ≤ p.asIdeal := by
    have hm := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) hxV).mp hx
    have hpre : p ∈ V.2.fromSpec ⁻¹' X.zeroLocus (I.ideal V : Set Γ(X, V)) := by
      change V.2.fromSpec p ∈ X.zeroLocus (I.ideal V : Set Γ(X, V))
      rwa [hp]
    rwa [V.2.fromSpec_preimage_zeroLocus] at hpre
  obtain ⟨C⟩ := Uniform.ClosedCarrierPointedLift.Construction.global_closed_carrier_uniform_center_chart_on_native_normal_open
    f I H hHI D B F hF V z hHz w hw N hNz p hIp
  let : Algebra ℂ C.chart.carrier := C.chart.algebra
  let T := Global.MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart.ofNativeCoordinateChart f I D V w hw F p C
  refine ⟨T, rfl, C.chart.point, ?_⟩
  change V.2.fromSpec (PrimeSpectrum.comap C.chart.map.toRingHom C.chart.point) = x
  rw [C.chart.point_over]
  exact hp

end

end OAI.AlgebraicGeometry.Resolution.Blowups

import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.HypersurfaceTransformNeighborhoods
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.PointedCenterSmooth
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalRegular
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothCenterBlowup

/-! # Smooth Hypersurface Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothHypersurfaceTransform.Construction

noncomputable section

/-! Blowing up any smooth center contained in a smooth Cartier hypersurface preserves smoothness of its actual transform. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem globalBlowup_smooth_controlled_hypersurface
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (I H : X.IdealSheafData) (hI : I ≠ ⊥) (hH : H ≠ ⊥)
    [Smooth (I.subschemeι ≫ f)] [Smooth (H.subschemeι ≫ f)]
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (hHI : H ≤ I) :
    Smooth ((GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).subschemeι ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)) := by
  apply GlobalBlowup.PointedCenterSmooth.Construction.globalBlowup_controlled_center_smooth_of_generating_neighborhoods f I H hI 1 (by simpa using hHI)
  intro x
  obtain ⟨U, hxU, z, hz, hHz⟩ := Locally.PrincipalRegular.Construction.locallyPrincipal_regular_generators H hH hlocal x
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  let : Algebra.Smooth ℂ (Γ(X, U) ⧸ I.ideal U) := SmoothCenterBlowup.Construction.idealSheaf_complex_smooth_center_quotient f I U
  let : Algebra.Smooth ℂ (Γ(X, U) ⧸ Ideal.span {z}) := by
    rw [← hHz]
    exact SmoothCenterBlowup.Construction.idealSheaf_complex_smooth_center_quotient f H U
  have hzI : z ∈ I.ideal U := (hHI U) (by rw [hHz]; exact Ideal.mem_span_singleton_self z)
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have hxrange : x ∈ U.2.fromSpec.opensRange := by rw [U.2.opensRange_fromSpec]; exact hxU
  obtain ⟨p, hp⟩ := hxrange
  obtain ⟨S, aS, hsS, φ, hφ, q, hq, κ, g, hg, hs⟩ :=
    Blowups.Smooth.HypersurfaceTransformNeighborhoods.Construction.smooth_hypersurface_transform_pointed_generators (k := ℂ) (I.ideal U) z hz hzI p
  refine ⟨U, S, aS, hsS, φ, hφ, q, ?_, κ, g, hg, ?_⟩
  · change U.2.fromSpec (PrimeSpectrum.comap φ.toRingHom q) = x
    rw [hq]
    exact hp
  · intro a
    rw [hHz]
    exact hs a

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothHypersurfaceTransform.Construction

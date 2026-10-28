import OAI.AlgebraicGeometry.Resolution.Blowups.PrincipalDifferentialSmoothness
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PointedSmoothCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalIdealSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealSheafIdentification

/-! # Principal Differential Smoothness -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.PrincipalDifferentialSmoothness.Construction

noncomputable section

/-! A unit first differential sheaf makes a locally principal closed subscheme smooth. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem locallyPrincipal_subscheme_smooth_of_firstDifferential_top
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (H : X.IdealSheafData)
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (h : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f H 1 = ⊤) :
    Smooth (H.subschemeι ≫ f) := by
  apply PointedSmoothCenter.Construction.idealSheaf_complex_center_smooth_of_pointed_open_charts H f
  intro x
  obtain ⟨U, hx, z, hz⟩ := hlocal x
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have hxrange : x ∈ U.2.fromSpec.opensRange := by
    rw [U.2.opensRange_fromSpec]
    exact hx
  obtain ⟨q, hq⟩ := hxrange
  refine ⟨.of Γ(X, U), inferInstance, U.2.fromSpec, inferInstance, ?_, q, hq,
    H.ideal U, Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel H U, ?_⟩
  · exact (Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U).symm
  · have hd := congrArg (fun I : X.IdealSheafData => I.ideal U) h
    change Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal ℂ (H.ideal U) = ⊤ at hd
    rw [hz] at hd ⊢
    exact PrincipalDifferentialSmoothness.Construction.smooth_principal_quotient_of_firstDifferential_top ℂ z hd

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.PrincipalDifferentialSmoothness.Construction

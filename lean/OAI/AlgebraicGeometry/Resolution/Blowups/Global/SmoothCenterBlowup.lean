import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AffineCenterBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Smooth
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.AffineCenter

/-! # Smooth Center Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothCenterBlowup.Construction

noncomputable section

/-! Every actual global blowup of a smooth nonzero closed center preserves ambient smoothness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem idealSheaf_complex_smooth_center_quotient
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)]
    (U : X.affineOpens) :
    letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    Algebra.Smooth ℂ (Γ(X, U) ⧸ I.ideal U) := by
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : IsOpenImmersion (I.subschemeCover.f U) := I.subschemeCover.openCover.map_prop U
  have hs : Smooth (I.subschemeCover.f U ≫ (I.subschemeι ≫ f)) := inferInstance
  rw [← Category.assoc, Scheme.IdealSheafData.subschemeCover_map_subschemeι] at hs
  change Smooth (((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) ≫
    U.2.isoSpec.inv) ≫ U.1.ι) ≫ f) at hs
  rw [Category.assoc] at hs
  change Smooth ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) ≫ U.2.fromSpec) ≫ f) at hs
  rw [Category.assoc, ← Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U, ← Spec.map_comp] at hs
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)
    (φ := CommRingCat.ofHom (algebraMap ℂ (Γ(X, U) ⧸ I.ideal U)))).mp hs)

theorem globalBlowup_smooth_of_smooth_center
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) [Smooth (I.subschemeι ≫ f)] :
    Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := by
  apply GlobalBlowup.Smooth.Construction.globalBlowup_smooth_of_affine_charts I hI f
  intro U
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  let : Algebra.Smooth ℂ (Γ(X, U) ⧸ I.ideal U) := idealSheaf_complex_smooth_center_quotient f I U
  rw [← Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U]
  exact Blowups.Smooth.AffineCenterBlowup.Construction.smooth_affine_center_blowup_smooth (I.ideal U)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothCenterBlowup.Construction

import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialIdealSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Data
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Affine Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.AffineCenter.Construction

noncomputable section

/-! Geometry of actual global centers and blowups checked on affine quotient charts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

/-- Smoothness of all actual affine center quotients proves smoothness of
the native closed subscheme, with its original map to the complex base. -/
theorem idealSheaf_complex_center_smooth_of_affine (I : X.IdealSheafData)
    (hlocal : ∀ U : X.affineOpens, letI := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
      Algebra.Smooth ℂ (Γ(X, U) ⧸ I.ideal U)) : Smooth (I.subschemeι ≫ f) := by
  let : IsZariskiLocalAtSource @Smooth :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_openCover I.subschemeCover.openCover
  intro U
  change X.affineOpens at U
  change Smooth (I.subschemeCover.f U ≫ (I.subschemeι ≫ f))
  rw [← Category.assoc, Scheme.IdealSheafData.subschemeCover_map_subschemeι]
  change Smooth (((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) ≫
    U.2.isoSpec.inv) ≫ U.1.ι) ≫ f)
  rw [Category.assoc]
  change Smooth ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) ≫ U.2.fromSpec) ≫ f)
  rw [Category.assoc]
  rw [← Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U, ← Spec.map_comp]
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  change (algebraMap ℂ (Γ(X, U) ⧸ I.ideal U)).Smooth
  exact RingHom.smooth_algebraMap.mpr (hlocal U)

variable [IsIntegral X] [IsLocallyNoetherian X]

omit f in
/-- If all affine Rees blowups are isomorphisms, so is the actual global
blowup assembled from them. -/
theorem globalBlowup_isIso_of_affine (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (hlocal : ∀ U : X.affineOpens, IsIso (ReesGrading.Construction.affineBlowupToSpec (I.ideal U))) :
    IsIso (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme)
    X.directedAffineCover
  intro U
  change X.affineOpens at U
  change IsIso (pullback.snd (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) U.1.ι)
  let : IsIso (ReesGrading.Construction.affineBlowupToSpec (I.ideal U)) := hlocal U
  rw [← (GlobalBlowup.Data.Construction.globalBlowup_affineOpen_isPullback I hI U).isoPullback_inv_snd]
  infer_instance

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.AffineCenter.Construction

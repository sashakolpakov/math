import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Data
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Smooth.Construction

noncomputable section

/-! Smoothness of the global Rees blowup from its actual affine charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Smooth affine blowup charts give smoothness of the already
constructed global scheme over its original base. -/
theorem globalBlowup_smooth_of_affine_charts
    {X Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (f : X ⟶ Z)
    (hcharts : ∀ U : X.affineOpens,
      Smooth (ReesGrading.Construction.affineBlowupToSpec (I.ideal U) ≫ U.2.fromSpec ≫ f)) :
    Smooth (Data.Construction.globalBlowupToBase I hI ≫ f) := by
  let : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth) (Data.Construction.blowupGluingData I hI).cover
  intro U
  change X.affineOpens at U
  change Smooth (Data.Construction.globalBlowupChart I hI U ≫ Data.Construction.globalBlowupToBase I hI ≫ f)
  rw [← Category.assoc, Data.Construction.globalBlowupChart_over, Category.assoc]
  exact hcharts U

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Smooth.Construction

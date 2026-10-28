import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.FlatBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoordinateBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SubsetCoordinateBlowup

/-! # Blowup Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.BlowupBaseChange.Construction

noncomputable section

/-! Smooth ambient base change of actual affine blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affineBlowupMap_smooth {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Smooth R S] (I : Ideal R) :
    Smooth (ReesMap.Construction.affineBlowupMap I (algebraMap R S)) := by
  have hbase : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact (RingHom.smooth_algebraMap (R := R) (S := S)).mpr inferInstance
  exact MorphismProperty.of_isPullback (P := @Smooth) (Blowup.FlatBaseChange.Construction.affineBlowup_flat_isPullback I).flip hbase

variable {R S σ : Type u} [CommRing R] [CommRing S] [Algebra (MvPolynomial σ R) S]
  [Algebra.Smooth (MvPolynomial σ R) S]

/-- An actual coordinate-center blowup remains smooth under any smooth
ambient map from its polynomial coordinate base. -/
theorem coordinateCenterBlowup_smooth_of_smooth [Finite σ] :
    Smooth (ReesGrading.Construction.affineBlowupToSpec ((MvPolynomial.idealOfVars σ R).map (algebraMap (MvPolynomial σ R) S)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial σ R) S)) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial σ R))) := by
  let : Smooth (ReesMap.Construction.affineBlowupMap (MvPolynomial.idealOfVars σ R) (algebraMap (MvPolynomial σ R) S)) :=
    affineBlowupMap_smooth (MvPolynomial.idealOfVars σ R)
  let : Smooth (ReesGrading.Construction.affineBlowupToSpec (MvPolynomial.idealOfVars σ R) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial σ R))) :=
    CoordinateBlowup.Construction.coordinateCenterBlowup_smooth
  rw [← Category.assoc, ← Blowup.BaseOpen.Construction.affineBlowupMap_over, Category.assoc]
  infer_instance

/-- The same smooth base-change argument applies to a selected coordinate subset. -/
theorem subsetCoordinateBlowup_smooth_of_smooth [Finite σ] [DecidableEq σ] (C : Finset σ) :
    Smooth (ReesGrading.Construction.affineBlowupToSpec ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ R) S)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial σ R) S)) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial σ R))) := by
  let : Smooth (ReesMap.Construction.affineBlowupMap (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (algebraMap (MvPolynomial σ R) S)) :=
    affineBlowupMap_smooth (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C)
  let : Smooth (ReesGrading.Construction.affineBlowupToSpec (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := R) C) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial σ R))) :=
    SubsetCoordinateBlowup.Construction.subsetCoordinateBlowup_smooth C
  rw [← Category.assoc, ← Blowup.BaseOpen.Construction.affineBlowupMap_over, Category.assoc]
  infer_instance

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.BlowupBaseChange.Construction

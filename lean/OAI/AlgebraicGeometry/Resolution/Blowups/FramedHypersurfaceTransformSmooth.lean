import OAI.AlgebraicGeometry.Resolution.Blowups.DualFrameBlowupSmooth
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.BlowupDimension
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BoundaryTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialHypersurface
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup

/-! # Framed Hypersurface Transform Smooth -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.FramedHypersurfaceTransformSmooth.Construction

noncomputable section

/-! Each actual generator chart of a smooth framed center has a smooth divided coordinate hypersurface. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem smooth_quotient_top {k A : Type u} [CommRing k] [CommRing A]
    [Algebra k A] [Algebra.Smooth k A] : Algebra.Smooth k (A ⧸ (⊤ : Ideal A)) := by
  let : Algebra.FormallySmooth k (A ⧸ (⊤ : Ideal A)) := ⟨inferInstance, inferInstance⟩
  let : Algebra.FinitePresentation k (A ⧸ (⊤ : Ideal A)) := Algebra.FinitePresentation.quotient (by
    rw [← Ideal.span_singleton_one]; exact Submodule.fg_span_singleton 1)
  exact ⟨inferInstance, inferInstance⟩

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem framed_coordinate_controlled_quotient_smooth
    {k R ι : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [Fintype ι] [DecidableEq ι] (I : Ideal R) (g : ι → I) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j).val = if i = j then 1 else 0)
    (hgen : Ideal.span (Set.range (fun i => (g i).val)) = I) (i j : ι) :
    Algebra.Smooth k (Blowup.Charts.Construction.blowupChart I (g i) ⧸ ControlledTransform.Construction.blowupControlledTransform I (Ideal.span {(g j).val}) 1 (g i)) := by
  have hbl := DualFrameBlowupSmooth.Construction.dual_derivation_family_blowup_smooth (fun j => (g j).val) D hD
  rw [hgen] at hbl
  let : Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))) := hbl
  let : Algebra.Smooth k (Blowup.Charts.Construction.blowupChart I (g i)) := Blowups.Smooth.BlowupChart.Construction.blowupChart_smooth_of_blowup_smooth k I (g i)
  rw [Coordinate.BoundaryTransform.Construction.blowup_principal_coordinate_controlledTransform I (g i) (g j)]
  by_cases hij : i = j
  · subst j
    rw [Etale.CoefficientStep.Construction.blowupChartRatio_self, Ideal.span_singleton_one]
    exact smooth_quotient_top
  · apply Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one (Relative.DifferentialBlowup.Construction.blowupRelativeChartDerivation k I (g i) (D j))
    exact Coordinate.BlowupTransform.Construction.blowupChartDerivation_coordinate I (g i) (g j) ((D j).restrictScalars ℤ)
      (by simpa only [Derivation.restrictScalars_apply, ite_eq_right (Ne.symm hij)] using hD j i)
      (by simpa only [Derivation.restrictScalars_apply, ite_true] using hD j j)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.FramedHypersurfaceTransformSmooth.Construction

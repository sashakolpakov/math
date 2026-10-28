import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Charts
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Blowup Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.BlowupChart.Construction

noncomputable section

/-! Smoothness on the actual coefficient rings of every denominator chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- A smooth actual blowup has smooth denominator-chart algebras over the
original coefficient ring, with the original coefficient maps retained. -/
theorem blowupChart_smooth_of_blowup_smooth (I : Ideal R)
    [Smooth (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))] (a : I) :
    Algebra.Smooth k (Blowup.Charts.Construction.blowupChart I a) := by
  have h : Smooth
      (Proj.awayι (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I a) (Blowup.Charts.Construction.reesGenerator_mem I a) (by decide) ≫
        (ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))) := inferInstance
  rw [← Category.assoc, Blowup.Charts.Construction.affineBlowup_chart_structureMap, ← Spec.map_comp] at h
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp h)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.BlowupChart.Construction

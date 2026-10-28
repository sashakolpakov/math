import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.AffineChartEquivalence
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Projective Chart Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.ProjectiveChartCover

noncomputable section

/-! Positive homogeneous elements of the Veronese algebra give
corresponding open covers of both projective spectra. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (g : ℕ → Submodule R A) [GradedAlgebra g] (N : ℕ) [NeZero N]

abbrev positiveVeroneseChartIndex := Σ d : {d : ℕ // 0 < d}, g (N * d.val)

def positiveVeroneseChartElement (j : positiveVeroneseChartIndex g N) : Subalgebra.veroneseSubalgebra g N :=
  ⟨j.2.val, Subalgebra.veronese_homogeneous_mem g N j.1.val j.2.property⟩

omit [NeZero N] in
theorem veronese_original_charts_cover (x : Proj g) :
    ∃ j : positiveVeroneseChartIndex g N, x ∈ Proj.basicOpen g j.2.val := by
  by_contra! H
  apply x.not_irrelevant_le
  apply (HomogeneousIdeal.irrelevant_le g).mpr
  intro d hd z hz
  have hpow : z ^ N ∈ g (N * d) := by
    simpa only [nsmul_eq_mul, Nat.cast_id] using (show z ^ N ∈ g (N • d) from SetLike.pow_mem_graded N (show z ∈ g d from hz))
  let j : positiveVeroneseChartIndex g N := ⟨⟨d, hd⟩, ⟨z ^ N, hpow⟩⟩
  have hp : z ^ N ∈ x.asHomogeneousIdeal := by
    simpa only [j, Proj.mem_basicOpen, not_not] using H j
  exact x.isPrime.mem_of_pow_mem N hp

theorem veronese_regraded_charts_cover (x : Proj (Grading.veroneseGrading g N)) :
    ∃ j : positiveVeroneseChartIndex g N,
      x ∈ Proj.basicOpen (Grading.veroneseGrading g N) (positiveVeroneseChartElement g N j) := by
  by_contra! H
  apply x.not_irrelevant_le
  apply (HomogeneousIdeal.irrelevant_le (Grading.veroneseGrading g N)).mpr
  intro d hd z hz
  let j : positiveVeroneseChartIndex g N := ⟨⟨d, hd⟩, ⟨z.val, hz⟩⟩
  have hp : positiveVeroneseChartElement g N j ∈ x.asHomogeneousIdeal := by
    simpa only [Proj.mem_basicOpen, not_not] using H j
  exact hp

def veroneseOriginalOpenCover : (Proj g).OpenCover where
  I₀ := positiveVeroneseChartIndex g N
  X j := (Proj.basicOpen g j.2.val).toScheme
  f j := (Proj.basicOpen g j.2.val).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨j, hj⟩ := veronese_original_charts_cover g N x
    exact ⟨j, ⟨⟨x, hj⟩, rfl⟩⟩

def veroneseRegradedOpenCover : (Proj (Grading.veroneseGrading g N)).OpenCover where
  I₀ := positiveVeroneseChartIndex g N
  X j := (Proj.basicOpen (Grading.veroneseGrading g N) (positiveVeroneseChartElement g N j)).toScheme
  f j := (Proj.basicOpen (Grading.veroneseGrading g N) (positiveVeroneseChartElement g N j)).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨j, hj⟩ := veronese_regraded_charts_cover g N x
    exact ⟨j, ⟨⟨x, hj⟩, rfl⟩⟩

def veroneseProjectiveChartIso (j : positiveVeroneseChartIndex g N) :
    (veroneseOriginalOpenCover g N).X j ≅ (veroneseRegradedOpenCover g N).X j :=
  Proj.basicOpenIsoSpec g j.2.val j.2.property
      (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne N)) j.1.property) ≪≫
    Scheme.Spec.mapIso (AffineChartEquivalence.veroneseAwayEquiv g N (positiveVeroneseChartElement g N j)
      (show positiveVeroneseChartElement g N j ∈ Grading.veroneseGrading g N j.1.val from j.2.property)).toCommRingCatIso.op ≪≫
    (Proj.basicOpenIsoSpec (Grading.veroneseGrading g N) (positiveVeroneseChartElement g N j)
      (show positiveVeroneseChartElement g N j ∈ Grading.veroneseGrading g N j.1.val from j.2.property)
      j.1.property).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.ProjectiveChartCover

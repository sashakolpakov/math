import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveMapAlgebraization
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Geometry.Manifold.Algebra.Structures

/-! # Projective Local Vectors -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveLocalVectors

noncomputable section

section

/-! Nonzero local homogeneous vectors with proportional overlaps
construct an actual continuous projective map. Holomorphic local vectors
give holomorphic projective coordinates on the original manifold. -/

open _root_.TopologicalSpace
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates Filter
open scoped _root_.Manifold ContDiff _root_.Topology

variable {M I : Type} [TopologicalSpace M] {n : ℕ}
    (U : I → Opens M) (hU : ∀ x, ∃ i, x ∈ U i)
    (v : I → M → (Fin (n + 1) → ℂ))
    (hv : ∀ i, ContinuousOn (v i) (U i))
    (hn : ∀ i x, x ∈ U i → v i x ≠ 0)
    (hc : ∀ i j x, x ∈ U i → x ∈ U j → ∃ c : ℂ, c • v j x = v i x)

def localProjectiveVectorMap (i : I) : C(U i, Projectivization ℂ (Fin (n + 1) → ℂ)) where
  toFun x := Projectivization.mk ℂ (v i x.val) (hn i x.val x.property)
  continuous_toFun := (ComplexPoints.Analytic.ProjectiveCompactness.continuous_projectivization_mk' ℂ (Fin (n + 1) → ℂ)).comp
    ((hv i).domRestrict.subtype_mk (fun x => hn i x.val x.property))

include hc in
theorem localProjectiveVectorMap_compatible (i j : I) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) :
    localProjectiveVectorMap U v hv hn i ⟨x, hi⟩ = localProjectiveVectorMap U v hv hn j ⟨x, hj⟩ :=
  (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr (hc i j x hi hj)

def gluedProjectiveVectorMap : C(M, Projectivization ℂ (Fin (n + 1) → ℂ)) :=
  ContinuousMap.liftCover (fun i => (U i : Set M)) (localProjectiveVectorMap U v hv hn)
    (localProjectiveVectorMap_compatible U v hv hn hc)
    (fun x => (hU x).imp (fun i hi => (U i).isOpen.mem_nhds hi))

theorem gluedProjectiveVectorMap_apply (i : I) (x : M) (hi : x ∈ U i) :
    gluedProjectiveVectorMap U hU v hv hn hc x = Projectivization.mk ℂ (v i x) (hn i x hi) := by
  unfold gluedProjectiveVectorMap
  exact ContinuousMap.liftCover_coe (S := fun i => (U i : Set M)) (i := i) (⟨x, hi⟩ : U i)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]

theorem gluedProjectiveVectorMap_holomorphic
    (hd : ∀ i, ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, Fin (n + 1) → ℂ) ∞ (v i) (U i))
    (j : Fin (n + 1)) (x : M)
    (hx : gluedProjectiveVectorMap U hU v hv hn hc x ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart j).source) :
    MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ)
      (fun y => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart j (gluedProjectiveVectorMap U hU v hv hn hc y)) x := by
  obtain ⟨i, hi⟩ := hU x
  have hj : v i x j ≠ 0 := by
    rw [gluedProjectiveVectorMap_apply U hU v hv hn hc i x hi] at hx
    exact (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff j _ _).mp hx
  have hvi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, Fin (n + 1) → ℂ) ∞ (v i) x :=
    (hd i x hi).contMDiffAt ((U i).isOpen.mem_nhds hi)
  have hr : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) ∞
      (fun y k => v i y (j.succAbove k) / v i y j) x := by
    apply contMDiffAt_pi_space.mpr
    intro k
    exact (contMDiffAt_pi_space.mp hvi (j.succAbove k)).div₀ (contMDiffAt_pi_space.mp hvi j) hj
  have he : (fun y => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart j (gluedProjectiveVectorMap U hU v hv hn hc y)) =ᶠ[𝓝 x]
      (fun y k => v i y (j.succAbove k) / v i y j) := by
    filter_upwards [(U i).isOpen.mem_nhds hi] with y hy
    rw [gluedProjectiveVectorMap_apply U hU v hv hn hc i y hy]
    rfl
  exact (hr.mdifferentiableAt (by simp)).congr_of_eventuallyEq he

end

section

/-! Two projective coordinate vectors and a nonzero comparison gauge
give one enlarged vector. Its overlap law retains every coordinate of
both original projective maps. -/

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

def comparisonCoordinateEquiv (n m : ℕ) :
    Fin (n + 1) ⊕ Fin (m + 1) ≃ Fin ((n + m + 1) + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

def projectiveComparisonVector {n m : ℕ}
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) (q : Projectivization ℂ (Fin (m + 1) → ℂ))
    (i : Fin (n + 1) × Fin (m + 1)) (g : ℂ) : Fin ((n + m + 1) + 1) → ℂ :=
  fun k => Sum.elim (fun a => Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 a p) (fun b => Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.2 b q / g)
    ((comparisonCoordinateEquiv n m).symm k)

theorem projectiveComparisonVector_left {n m : ℕ}
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) (q : Projectivization ℂ (Fin (m + 1) → ℂ))
    (i : Fin (n + 1) × Fin (m + 1)) (g : ℂ) (j : Fin (n + 1)) :
    projectiveComparisonVector p q i g (comparisonCoordinateEquiv n m (.inl j)) = Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 j p := by
  simp only [projectiveComparisonVector, Equiv.symm_apply_apply, Sum.elim_inl]

theorem projectiveComparisonVector_right {n m : ℕ}
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) (q : Projectivization ℂ (Fin (m + 1) → ℂ))
    (i : Fin (n + 1) × Fin (m + 1)) (g : ℂ) (j : Fin (m + 1)) :
    projectiveComparisonVector p q i g (comparisonCoordinateEquiv n m (.inr j)) = Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.2 j q / g := by
  simp only [projectiveComparisonVector, Equiv.symm_apply_apply, Sum.elim_inr]

theorem projectiveComparisonVector_ne_zero {n m : ℕ}
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) (q : Projectivization ℂ (Fin (m + 1) → ℂ))
    (i : Fin (n + 1) × Fin (m + 1)) (g : ℂ) (hi : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i.1 p) :
    projectiveComparisonVector p q i g ≠ 0 := by
  apply Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.normalized_ne_zero (comparisonCoordinateEquiv n m (.inl i.1))
  exact (projectiveComparisonVector_left p q i g i.1).trans hi

theorem comparisonGauge_scaled_ratio (a b c d z : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (he : a / b = d / c) : a * ((z / b) / d) = z / c := by
  have h := (div_eq_div_iff hb hc).mp he
  rw [div_div, show b * d = a * c from (mul_comm b d).trans h.symm]
  field_simp [ha, hc]

theorem projectiveComparisonVector_change {n m : ℕ}
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) (q : Projectivization ℂ (Fin (m + 1) → ℂ))
    (i j : Fin (n + 1) × Fin (m + 1)) (g h : ℂ)
    (hi : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i.1 p) (hj : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j.1 p) (hi' : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i.2 q) (hj' : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j.2 q)
    (hg : g ≠ 0) (he : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 j.1 p / Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.2 j.2 q = h / g) :
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 j.1 p • projectiveComparisonVector p q j h = projectiveComparisonVector p q i g := by
  have ha := (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero i.1 j.1 p hi).mp hj
  have hb := (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero i.2 j.2 q hi').mp hj'
  funext k
  obtain ⟨k, rfl⟩ := (comparisonCoordinateEquiv n m).surjective k
  cases k with
  | inl k =>
    simp only [Pi.smul_apply, smul_eq_mul, projectiveComparisonVector_left]
    rw [Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.transition_formula i.1 j.1 k p hi]
    exact mul_div_cancel₀ _ ha
  | inr k =>
    simp only [Pi.smul_apply, smul_eq_mul, projectiveComparisonVector_right]
    rw [Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.transition_formula i.2 j.2 k q hi']
    exact comparisonGauge_scaled_ratio _ _ _ _ _ ha hb hg he

end

/-! Enlarged projective vectors for section graphs retain a nonzero
first block even where the section vanishes. Their overlap law uses
multiplication by the local section coefficient. -/

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

def projectiveSectionVector {n m : ℕ}
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) (q : Projectivization ℂ (Fin (m + 1) → ℂ))
    (i : Fin (n + 1) × Fin (m + 1)) (c : ℂ) : Fin ((n + m + 1) + 1) → ℂ :=
  fun k => Sum.elim (fun a => Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 a p) (fun b => Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.2 b q * c)
    ((comparisonCoordinateEquiv n m).symm k)

theorem projectiveSectionVector_left {n m : ℕ}
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) (q : Projectivization ℂ (Fin (m + 1) → ℂ))
    (i : Fin (n + 1) × Fin (m + 1)) (c : ℂ) (j : Fin (n + 1)) :
    projectiveSectionVector p q i c (comparisonCoordinateEquiv n m (.inl j)) = Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 j p := by
  simp only [projectiveSectionVector, Equiv.symm_apply_apply, Sum.elim_inl]

theorem projectiveSectionVector_right {n m : ℕ}
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) (q : Projectivization ℂ (Fin (m + 1) → ℂ))
    (i : Fin (n + 1) × Fin (m + 1)) (c : ℂ) (j : Fin (m + 1)) :
    projectiveSectionVector p q i c (comparisonCoordinateEquiv n m (.inr j)) = Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.2 j q * c := by
  simp only [projectiveSectionVector, Equiv.symm_apply_apply, Sum.elim_inr]

theorem projectiveSectionVector_ne_zero {n m : ℕ}
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) (q : Projectivization ℂ (Fin (m + 1) → ℂ))
    (i : Fin (n + 1) × Fin (m + 1)) (c : ℂ) (hi : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i.1 p) :
    projectiveSectionVector p q i c ≠ 0 := by
  apply Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.normalized_ne_zero (comparisonCoordinateEquiv n m (.inl i.1))
  exact (projectiveSectionVector_left p q i c i.1).trans hi

theorem sectionCoefficient_scaled_ratio (a b c d z : ℂ) (hb : b ≠ 0)
    (he : a * d = b * c) : a * ((z / b) * d) = z * c := by
  calc
    _ = (z / b) * (a * d) := by ring
    _ = (z / b) * (b * c) := congrArg ((z / b) * ·) he
    _ = _ := by rw [← mul_assoc, div_mul_cancel₀ _ hb]

theorem projectiveSectionVector_change {n m : ℕ}
    (p : Projectivization ℂ (Fin (n + 1) → ℂ)) (q : Projectivization ℂ (Fin (m + 1) → ℂ))
    (i j : Fin (n + 1) × Fin (m + 1)) (c d : ℂ)
    (hi : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i.1 p) (hj : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j.1 p) (hi' : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i.2 q) (hj' : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j.2 q)
    (he : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 j.1 p * d = Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.2 j.2 q * c) :
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i.1 j.1 p • projectiveSectionVector p q j d = projectiveSectionVector p q i c := by
  have ha := (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero i.1 j.1 p hi).mp hj
  have hb := (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero i.2 j.2 q hi').mp hj'
  funext k
  obtain ⟨k, rfl⟩ := (comparisonCoordinateEquiv n m).surjective k
  cases k with
  | inl k =>
    simp only [Pi.smul_apply, smul_eq_mul, projectiveSectionVector_left]
    rw [Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.transition_formula i.1 j.1 k p hi]
    exact mul_div_cancel₀ _ ha
  | inr k =>
    simp only [Pi.smul_apply, smul_eq_mul, projectiveSectionVector_right]
    rw [Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.transition_formula i.2 j.2 k q hi']
    exact sectionCoefficient_scaled_ratio _ _ _ _ _ hb he

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveLocalVectors

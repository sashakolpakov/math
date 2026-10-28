import OAI.RepresentationTheory.Theta.Geometric.AutomorphicFamilyConstructors
import OAI.RepresentationTheory.Theta.Geometric.OddSections
import OAI.RepresentationTheory.Theta.Geometric.Torus.Root

/-! # Odd Embedding -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! An odd power of the original polarization gives an embedding, by
multiplying its generators with the existing even theta embedding. -/

open scoped ContDiff

variable {Φ : Torus.Data.CM.ProjectivePeriodData}

theorem OddEmbedding.CM.Torus.AutomorphicTheta.exists_odd_embedding
    (H : Φ.space →ₗ⋆[ℂ] Φ.space →ₗ[ℂ] ℂ)
    (hsym : ∀ u v, H v u = star (H u v))
    (hpos : ∀ u, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Φ.periodIntegerLattice, ∀ v ∈ Φ.periodIntegerLattice,
      ∃ m : ℤ, (H u v).im = (m : ℝ))
    (J : Φ.AutomorphyFactor) (hJ : ∀ l, ContDiff ℂ ∞ (J.value l))
    (hsq : ∀ (l : Φ.periodIntegerLattice) z, J.value l z ^ 2 = Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy H l.val z)
    (hdouble : ∀ l : Φ.periodIntegerLattice, l ∈ Φ.doubleSubgroup → ∀ z,
      J.value l z = Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy (Φ.halfHermitian H) l.val z) :
    ∃ F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J, Odd F.degree ∧ 0 < F.degree ∧ Function.Injective F.projectiveMap ∧
      ∀ p v : Φ.space, v ≠ 0 → F.Detects p v := by
  let : DiscreteTopology Φ.periodIntegerLattice.toAddSubgroup := Φ.periodIntegerLattice_discrete
  obtain ⟨F, hFi, hFd⟩ := Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.exists_injective_immersive_family H Φ.periodIntegerLattice.toAddSubgroup
    hsym hpos hint
  obtain ⟨n, hn, hnpos, hgen⟩ := Φ.exists_odd_generated_power H hsym hpos hint J hJ hdouble
  obtain ⟨S, hreg, htrans, hnonzero⟩ := (J.power n).exists_finite_generators hgen
  let E := AutomorphicFamilyConstructors.CM.Torus.AutomorphicTheta.evenThetaFamily H J hsq F
  let G := AutomorphicFamilyConstructors.CM.Torus.AutomorphicTheta.familyOfFunctions J n S hreg htrans hnonzero
  refine ⟨E.mul G, ?_, ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hn
    exact ⟨F.degree + k, by change 2 * F.degree + n = _; omega⟩
  · change 0 < 2 * F.degree + n
    omega
  · intro p q hpq
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective p
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
    apply AutomorphicFamilyConstructors.CM.Torus.AutomorphicTheta.evenThetaFamily_injective H J hsq F hFi
    apply (E.projectiveMap_eq_of_not_separates v w).mpr
    intro hsep
    exact ((E.mul G).projectiveMap_eq_of_not_separates v w).mp hpq (E.separates_mul_left G v w hsep)
  · intro p v hv
    exact E.detects_mul_left G p v (AutomorphicFamilyConstructors.CM.Torus.AutomorphicTheta.evenThetaFamily_detects H J hsq F p v (hFd p v hv))

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

variable {J : Φ.AutomorphyFactor}

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.projective_all_charts (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hF : ∀ p v : Φ.space, v ≠ 0 → F.Detects p v)
    (z : Φ.space) (i : Fin (F.projectiveDimension + 1))
    (hi : F.projectiveMap (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source) :
    DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (F.projectiveMap (QuotientAddGroup.mk w))) z ∧
    Function.Injective (fderiv ℂ
      (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (F.projectiveMap (QuotientAddGroup.mk w))) z) := by
  have hip := (F.projectiveMap_inPatch i z).mp hi
  have hc : ContinuousAt (fun w : Φ.space => F.projectiveMap (QuotientAddGroup.mk w)) z :=
    (F.projectiveMap_continuous.comp QuotientAddGroup.continuous_mk).continuousAt
  have hd : DifferentiableAt ℂ
      (fun w : Φ.space => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (F.projectiveMap (QuotientAddGroup.mk w))) z := by
    simp_rw [F.projectiveMap_coordinates]
    exact (F.chart_contDiffAt i z hip).differentiableAt (by norm_num)
  have hinj : Function.Injective (fderiv ℂ
      (fun w : Φ.space => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (F.projectiveMap (QuotientAddGroup.mk w))) z) := by
    simp_rw [F.projectiveMap_coordinates]
    exact F.chart_fderiv_injective z (hF z) i hip
  exact ⟨Geometry.ComplexTorus.RiemannProjectivity.Fin.Constructions.projectiveFinChart_differentiableAt _ i hd,
    Geometry.ComplexTorus.RiemannProjectivity.Fin.Constructions.projectiveFinChart_injective_fderiv _ hc i hi hd hinj⟩

end

end OAI.RepresentationTheory.Theta.Geometric

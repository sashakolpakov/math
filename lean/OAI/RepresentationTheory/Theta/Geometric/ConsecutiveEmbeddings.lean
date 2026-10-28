import OAI.RepresentationTheory.Theta.Geometric.OddEmbedding
import OAI.RepresentationTheory.Theta.Geometric.ConsecutiveSections

/-! # Consecutive Embeddings -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Two consecutive powers give embeddings of the same original period torus. -/

open scoped ContDiff

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.mul_injective (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hF : Function.Injective F.projectiveMap) :
    Function.Injective (F.mul G).projectiveMap := by
  intro p q hpq
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective p
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
  apply hF
  apply (F.projectiveMap_eq_of_not_separates v w).mpr
  intro hsep
  exact ((F.mul G).projectiveMap_eq_of_not_separates v w).mp hpq (F.separates_mul_left G v w hsep)

theorem ConsecutiveEmbeddings.CM.Torus.AutomorphicTheta.family_of_generated_power (n : ℕ) (h : J.GeneratedPower Φ n) :
    ∃ F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J, F.degree = n := by
  obtain ⟨S, hreg, htrans, hnonzero⟩ := (J.power n).exists_finite_generators h
  exact ⟨AutomorphicFamilyConstructors.CM.Torus.AutomorphicTheta.familyOfFunctions J n S hreg htrans hnonzero, rfl⟩

theorem ConsecutiveEmbeddings.CM.Torus.AutomorphicTheta.exists_consecutive_embeddings
    (H : Φ.space →ₗ⋆[ℂ] Φ.space →ₗ[ℂ] ℂ)
    (hsym : ∀ u v, H v u = star (H u v))
    (hpos : ∀ u, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Φ.periodIntegerLattice, ∀ v ∈ Φ.periodIntegerLattice,
      ∃ m : ℤ, (H u v).im = (m : ℝ))
    (J : Φ.AutomorphyFactor) (hJ : ∀ l, ContDiff ℂ ∞ (J.value l))
    (hsq : ∀ (l : Φ.periodIntegerLattice) z, J.value l z ^ 2 = Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy H l.val z)
    (hdouble : ∀ l : Φ.periodIntegerLattice, l ∈ Φ.doubleSubgroup → ∀ z,
      J.value l z = Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy (Φ.halfHermitian H) l.val z) :
    ∃ F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J,
      0 < F.degree ∧ G.degree = F.degree + 1 ∧
      Function.Injective F.projectiveMap ∧ Function.Injective G.projectiveMap ∧
      (∀ p v : Φ.space, v ≠ 0 → F.Detects p v) ∧
      ∀ p v : Φ.space, v ≠ 0 → G.Detects p v := by
  let : DiscreteTopology Φ.periodIntegerLattice.toAddSubgroup := Φ.periodIntegerLattice_discrete
  obtain ⟨B, hBi, hBd⟩ := Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.exists_injective_immersive_family H Φ.periodIntegerLattice.toAddSubgroup
    hsym hpos hint
  let E := AutomorphicFamilyConstructors.CM.Torus.AutomorphicTheta.evenThetaFamily H J hsq B
  have hEi := AutomorphicFamilyConstructors.CM.Torus.AutomorphicTheta.evenThetaFamily_injective H J hsq B hBi
  have hEd := fun p v hv => AutomorphicFamilyConstructors.CM.Torus.AutomorphicTheta.evenThetaFamily_detects H J hsq B p v (hBd p v hv)
  obtain ⟨n, hn, h0, h1⟩ := Φ.exists_consecutive_generated_powers H hsym hpos hint J hJ hdouble
  obtain ⟨F, hF⟩ := ConsecutiveEmbeddings.CM.Torus.AutomorphicTheta.family_of_generated_power n h0
  obtain ⟨G, hG⟩ := ConsecutiveEmbeddings.CM.Torus.AutomorphicTheta.family_of_generated_power (n + 1) h1
  refine ⟨E.mul F, E.mul G, ?_, ?_, E.mul_injective F hEi, E.mul_injective G hEi, ?_, ?_⟩
  · change 0 < E.degree + F.degree
    omega
  · change E.degree + G.degree = E.degree + F.degree + 1
    omega
  · exact fun p v hv => E.detects_mul_left F p v (hEd p v hv)
  · exact fun p v hv => E.detects_mul_left G p v (hEd p v hv)

end

end OAI.RepresentationTheory.Theta.Geometric

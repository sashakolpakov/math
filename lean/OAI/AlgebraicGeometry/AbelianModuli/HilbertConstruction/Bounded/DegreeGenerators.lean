import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.IdealExtension

/-! # Degree Generators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A split quotient of a finite free degree module supplies a uniformly indexed generating family for its relations. -/

universe u v w

theorem Bounded.DegreeGenerators.submodule_generators_of_projective_quotient {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V] {ι : Type w}
    (b : Module.Basis ι R V) (K : Submodule R V) [Module.Projective R (V ⧸ K)] :
    ∃ g : ι → V, Submodule.span R (Set.range g) = K := by
  obtain ⟨s, hs⟩ := K.mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr K.mkQ_surjective)
  let L : V →ₗ[R] V := LinearMap.id - s.comp K.mkQ
  have hL : L.range = K := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero K).mp
      have he := LinearMap.congr_fun hs (K.mkQ y)
      change K.mkQ (s (K.mkQ y)) = K.mkQ y at he
      change K.mkQ (y - s (K.mkQ y)) = 0
      rw [map_sub, he, sub_self]
    · intro x hx
      refine ⟨x, ?_⟩
      change x - s (K.mkQ x) = x
      have hx0 : K.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hx
      rw [hx0, map_zero, sub_zero]
  refine ⟨fun i => L (b i), ?_⟩
  rw [show Set.range (fun i => L (b i)) = L '' Set.range b from Set.range_comp L b]
  rw [← Submodule.map_span, b.span_eq, Submodule.map_top, hL]

variable {R : Type u} [CommRing R] {σ : Type v} {B : ℕ} {r : ℕ → ℕ}
variable (D : Truncated.GradedClassification.TruncatedGradedQuotientData R σ B r) (d : Fin (B + 1))

def Truncated.GradedClassification.TruncatedGradedQuotientData.degreeGenerators : Homogeneous.Coordinates.HomogeneousMonomials σ d → MvPolynomial.homogeneousSubmodule σ R d :=
  (Bounded.DegreeGenerators.submodule_generators_of_projective_quotient (Homogeneous.Coordinates.homogeneousMonomialBasis R σ d)
    (D.quotient d).toSubmodule).choose

theorem Truncated.GradedClassification.TruncatedGradedQuotientData.degreeGenerators_span :
    Submodule.span R (Set.range (D.degreeGenerators d)) = (D.quotient d).toSubmodule :=
  (Bounded.DegreeGenerators.submodule_generators_of_projective_quotient (Homogeneous.Coordinates.homogeneousMonomialBasis R σ d)
    (D.quotient d).toSubmodule).choose_spec

theorem Truncated.GradedClassification.TruncatedGradedQuotientData.degreeGenerators_mem (i : Homogeneous.Coordinates.HomogeneousMonomials σ d) :
    D.degreeGenerators d i ∈ (D.quotient d).toSubmodule := by
  rw [← D.degreeGenerators_span d]
  exact Submodule.subset_span (Set.mem_range_self i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

import OAI.Analysis.HodgeTheory.Decomposition.AdjointAlgebra
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Energy Domain -/

namespace OAI.Analysis.HodgeTheory.Decomposition.EnergyDomain.Constructions

noncomputable section

section

/-! The actual Hilbert graph domain of exterior differentiation and its
constructed codifferential. Integration by parts proves that its projection
into L² is injective, so graph completion introduces no spurious derivatives. -/

open scoped _root_.Manifold

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

abbrev ProjectiveEnergyValues := WithLp 2 (Form.Constructions.ProjectiveL2Forms V (n + 1 + 1) × Form.Constructions.ProjectiveL2Forms V n)
abbrev ProjectiveGraphAmbient := WithLp 2 (Form.Constructions.ProjectiveL2Forms V (n + 1) × ProjectiveEnergyValues V n)

def projectiveGraphEmbedding :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1) →ₗ[ℂ] ProjectiveGraphAmbient V n :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap.comp
    ((Form.Constructions.smoothToProjectiveL2 V (n + 1)).prod
      ((WithLp.linearEquiv 2 ℂ _).symm.toLinearMap.comp
        (((Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1)).comp DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d).prod
          ((Form.Constructions.smoothToProjectiveL2 V n).comp (AdjointAlgebra.Constructions.projectiveCodifferential V n)))))

abbrev ProjectiveEnergyDomain := (projectiveGraphEmbedding V n).range.topologicalClosure

def projectiveGraphValue : ProjectiveGraphAmbient V n →L[ℂ] Form.Constructions.ProjectiveL2Forms V (n + 1) :=
  WithLp.fstL 2 ℂ _ _

def projectiveGraphD : ProjectiveGraphAmbient V n →L[ℂ] Form.Constructions.ProjectiveL2Forms V (n + 1 + 1) :=
  (WithLp.fstL 2 ℂ _ _).comp (WithLp.sndL 2 ℂ _ _)

def projectiveGraphDelta : ProjectiveGraphAmbient V n →L[ℂ] Form.Constructions.ProjectiveL2Forms V n :=
  (WithLp.sndL 2 ℂ _ _).comp (WithLp.sndL 2 ℂ _ _)

/-- Integration by parts persists in the completed graph domain. -/
theorem projectiveEnergyDomain_d_pair (u : ProjectiveEnergyDomain V n)
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1 + 1)) :
    inner ℂ (Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1) b) (projectiveGraphD V n u.val) =
      inner ℂ (Form.Constructions.smoothToProjectiveL2 V (n + 1) (AdjointAlgebra.Constructions.projectiveCodifferential V (n + 1) b))
        (projectiveGraphValue V n u.val) := by
  have hclosed : IsClosed {x : ProjectiveGraphAmbient V n |
      inner ℂ (Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1) b) (projectiveGraphD V n x) =
        inner ℂ (Form.Constructions.smoothToProjectiveL2 V (n + 1) (AdjointAlgebra.Constructions.projectiveCodifferential V (n + 1) b))
          (projectiveGraphValue V n x)} :=
    isClosed_eq (continuous_const.inner (projectiveGraphD V n).continuous)
      (continuous_const.inner (projectiveGraphValue V n).continuous)
  apply closure_minimal (s := Set.range (projectiveGraphEmbedding V n)) _ hclosed u.property
  rintro x ⟨a, rfl⟩
  change inner ℂ (Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1) b)
    (Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)) =
      inner ℂ (Form.Constructions.smoothToProjectiveL2 V (n + 1) (AdjointAlgebra.Constructions.projectiveCodifferential V (n + 1) b))
        (Form.Constructions.smoothToProjectiveL2 V (n + 1) a)
  rw [Form.Constructions.smoothToProjectiveL2_inner, Form.Constructions.smoothToProjectiveL2_inner, AdjointAlgebra.Constructions.projectiveCodifferential_pair]

theorem projectiveEnergyDomain_delta_pair (u : ProjectiveEnergyDomain V n)
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    inner ℂ (Form.Constructions.smoothToProjectiveL2 V n b) (projectiveGraphDelta V n u.val) =
      inner ℂ (Form.Constructions.smoothToProjectiveL2 V (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b))
        (projectiveGraphValue V n u.val) := by
  have hclosed : IsClosed {x : ProjectiveGraphAmbient V n |
      inner ℂ (Form.Constructions.smoothToProjectiveL2 V n b) (projectiveGraphDelta V n x) =
        inner ℂ (Form.Constructions.smoothToProjectiveL2 V (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b))
          (projectiveGraphValue V n x)} :=
    isClosed_eq (continuous_const.inner (projectiveGraphDelta V n).continuous)
      (continuous_const.inner (projectiveGraphValue V n).continuous)
  apply closure_minimal (s := Set.range (projectiveGraphEmbedding V n)) _ hclosed u.property
  rintro x ⟨a, rfl⟩
  change inner ℂ (Form.Constructions.smoothToProjectiveL2 V n b) (Form.Constructions.smoothToProjectiveL2 V n (AdjointAlgebra.Constructions.projectiveCodifferential V n a)) =
      inner ℂ (Form.Constructions.smoothToProjectiveL2 V (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b)) (Form.Constructions.smoothToProjectiveL2 V (n + 1) a)
  rw [Form.Constructions.smoothToProjectiveL2_inner, Form.Constructions.smoothToProjectiveL2_inner, AdjointAlgebra.Constructions.projectiveCodifferential_pair_right]

def projectiveEnergyInclusion : ProjectiveEnergyDomain V n →L[ℂ] Form.Constructions.ProjectiveL2Forms V (n + 1) :=
  (projectiveGraphValue V n).comp (ProjectiveEnergyDomain V n).subtypeL

def projectiveEnergyDerivative : ProjectiveEnergyDomain V n →L[ℂ] ProjectiveEnergyValues V n :=
  (WithLp.sndL 2 ℂ _ _).comp (ProjectiveEnergyDomain V n).subtypeL

/-- The graph completion retains the actual L² value uniquely. -/
theorem projectiveEnergyInclusion_injective : Function.Injective (projectiveEnergyInclusion V n) := by
  have hzero (u : ProjectiveEnergyDomain V n) (hu : projectiveEnergyInclusion V n u = 0) : u = 0 := by
    have hv : projectiveGraphValue V n u.val = 0 := hu
    have hd : projectiveGraphD V n u.val = 0 := by
      apply (Form.Constructions.smoothToProjectiveL2_dense V (n + 1 + 1)).eq_zero_of_inner_right ℂ
      intro b
      rw [projectiveEnergyDomain_d_pair, hv, inner_zero_right]
    have hδ : projectiveGraphDelta V n u.val = 0 := by
      apply (Form.Constructions.smoothToProjectiveL2_dense V n).eq_zero_of_inner_right ℂ
      intro b
      rw [projectiveEnergyDomain_delta_pair, hv, inner_zero_right]
    apply Subtype.ext
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · exact hv
    · apply (WithLp.equiv 2 _).injective
      exact Prod.ext hd hδ
  intro u v huv
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, huv, sub_self]

theorem projectiveEnergyInclusion_dense : DenseRange (projectiveEnergyInclusion V n) := by
  apply (Form.Constructions.smoothToProjectiveL2_dense V (n + 1)).mono
  rintro x ⟨a, rfl⟩
  refine ⟨⟨projectiveGraphEmbedding V n a, ?_⟩, rfl⟩
  exact (projectiveGraphEmbedding V n).range.le_topologicalClosure ⟨a, rfl⟩

/-- The completed graph inner product is exactly L² plus the actual differential energy. -/
theorem projectiveEnergyDomain_inner (u v : ProjectiveEnergyDomain V n) :
    inner ℂ u v =
      inner ℂ (projectiveEnergyInclusion V n u) (projectiveEnergyInclusion V n v) +
        inner ℂ (projectiveEnergyDerivative V n u) (projectiveEnergyDerivative V n v) := rfl

end

/-! The graph norm of a genuine smooth form is exactly its actual Hodge energy. -/

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

theorem projectiveGraphEmbedding_norm_sq
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    ‖projectiveGraphEmbedding V n a‖ ^ 2 =
      ‖Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)‖ ^ 2 +
        ‖Form.Constructions.smoothToProjectiveL2 V n (AdjointAlgebra.Constructions.projectiveCodifferential V n a)‖ ^ 2 +
        ‖Form.Constructions.smoothToProjectiveL2 V (n + 1) a‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change ‖Form.Constructions.smoothToProjectiveL2 V (n + 1) a‖ ^ 2 +
    (‖Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)‖ ^ 2 +
      ‖Form.Constructions.smoothToProjectiveL2 V n (AdjointAlgebra.Constructions.projectiveCodifferential V n a)‖ ^ 2) = _
  ring

theorem projectiveGraphEmbedding_value_norm_sq_le
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    ‖Form.Constructions.smoothToProjectiveL2 V (n + 1) a‖ ^ 2 ≤ ‖projectiveGraphEmbedding V n a‖ ^ 2 := by
  rw [projectiveGraphEmbedding_norm_sq]
  exact le_add_of_nonneg_left (add_nonneg (sq_nonneg _) (sq_nonneg _))

end

end OAI.Analysis.HodgeTheory.Decomposition.EnergyDomain.Constructions

import OAI.Analysis.HodgeTheory.Decomposition.AdjointManifold

/-! # Adjoint Algebra -/

namespace OAI.Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions

noncomputable section

section

/-! Algebraic consequences of the proved global formal-adjoint identity. -/

open scoped _root_.Manifold

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

theorem projectiveL2Pair_sub_left
    (a b c : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    Form.Constructions.projectiveL2Pair V n (a - b) c = Form.Constructions.projectiveL2Pair V n a c - Form.Constructions.projectiveL2Pair V n b c := by
  rw [← Form.Constructions.smoothToProjectiveL2_inner, map_sub, inner_sub_left,
    Form.Constructions.smoothToProjectiveL2_inner, Form.Constructions.smoothToProjectiveL2_inner]

theorem projectiveL2Pair_zero_left
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) : Form.Constructions.projectiveL2Pair V n 0 a = 0 := by
  rw [← Form.Constructions.smoothToProjectiveL2_inner, map_zero, inner_zero_left]

theorem projectiveL2Pair_zero_right
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) : Form.Constructions.projectiveL2Pair V n a 0 = 0 := by
  rw [← Form.Constructions.smoothToProjectiveL2_inner, map_zero, inner_zero_right]

theorem projectiveL2Pair_separates_left
    (a b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (h : ∀ u, Form.Constructions.projectiveL2Pair V n a u = Form.Constructions.projectiveL2Pair V n b u) : a = b := by
  apply sub_eq_zero.mp
  apply Form.Constructions.projectiveL2Pair_definite V n
  rw [projectiveL2Pair_sub_left, h (a - b), sub_self]

/-- The genuine L² adjoint is uniquely determined, independently of the chosen partition. -/
theorem projectiveGlobalAdjoint_unique
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (c : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (h : ∀ a, Form.Constructions.projectiveL2Pair V (n + 1) b (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) = Form.Constructions.projectiveL2Pair V n c a) :
    c = AdjointManifold.Constructions.projectiveGlobalAdjoint V n b := by
  apply projectiveL2Pair_separates_left V n
  intro a
  rw [← h a, AdjointManifold.Constructions.projectiveGlobalAdjoint_pair]

theorem projectiveGlobalAdjoint_add
    (b c : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    AdjointManifold.Constructions.projectiveGlobalAdjoint V n (b + c) = AdjointManifold.Constructions.projectiveGlobalAdjoint V n b + AdjointManifold.Constructions.projectiveGlobalAdjoint V n c := by
  apply projectiveL2Pair_separates_left V n
  intro a
  rw [← AdjointManifold.Constructions.projectiveGlobalAdjoint_pair, Form.Constructions.projectiveL2Pair_add_left, Form.Constructions.projectiveL2Pair_add_left,
    AdjointManifold.Constructions.projectiveGlobalAdjoint_pair, AdjointManifold.Constructions.projectiveGlobalAdjoint_pair]

theorem projectiveGlobalAdjoint_smul
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) (z : ℂ) :
    AdjointManifold.Constructions.projectiveGlobalAdjoint V n (z • b) = z • AdjointManifold.Constructions.projectiveGlobalAdjoint V n b := by
  apply projectiveL2Pair_separates_left V n
  intro a
  rw [← AdjointManifold.Constructions.projectiveGlobalAdjoint_pair, Form.Constructions.projectiveL2Pair_smul_left, Form.Constructions.projectiveL2Pair_smul_left,
    AdjointManifold.Constructions.projectiveGlobalAdjoint_pair]

/-- The actual codifferential, now bundled as a complex-linear map. -/
def projectiveCodifferential :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1) →ₗ[ℂ]
      DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n where
  toFun := AdjointManifold.Constructions.projectiveGlobalAdjoint V n
  map_add' := projectiveGlobalAdjoint_add V n
  map_smul' := fun z b => projectiveGlobalAdjoint_smul V n b z

theorem projectiveCodifferential_pair
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    Form.Constructions.projectiveL2Pair V (n + 1) b (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) =
      Form.Constructions.projectiveL2Pair V n (projectiveCodifferential V n b) a :=
  AdjointManifold.Constructions.projectiveGlobalAdjoint_pair V n a b

theorem projectiveCodifferential_pair_right
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    Form.Constructions.projectiveL2Pair V (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) b =
      Form.Constructions.projectiveL2Pair V n a (projectiveCodifferential V n b) := by
  rw [← Form.Constructions.projectiveL2Pair_symm, projectiveCodifferential_pair, Form.Constructions.projectiveL2Pair_symm]

/-- Squaring the codifferential gives zero because the actual exterior derivative squares to zero. -/
theorem projectiveCodifferential_squared
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1 + 1)) :
    projectiveCodifferential V n (projectiveCodifferential V (n + 1) b) = 0 := by
  apply projectiveL2Pair_separates_left V n
  intro a
  rw [← projectiveCodifferential_pair, ← projectiveCodifferential_pair,
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_squared, projectiveL2Pair_zero_right, projectiveL2Pair_zero_left]

/-- The Hodge Laplacian on positive-degree genuine smooth forms. -/
def projectivePositiveLaplacian :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1) →ₗ[ℂ]
      DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1) :=
  DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d.comp (projectiveCodifferential V n) +
    (projectiveCodifferential V (n + 1)).comp DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d

/-- The actual Laplacian energy is the sum of the two actual squared L² norms. -/
theorem projectivePositiveLaplacian_energy
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    Form.Constructions.projectiveL2Pair V (n + 1) (projectivePositiveLaplacian V n a) a =
      Form.Constructions.projectiveL2Pair V n (projectiveCodifferential V n a) (projectiveCodifferential V n a) +
        Form.Constructions.projectiveL2Pair V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) := by
  change Form.Constructions.projectiveL2Pair V (n + 1)
    (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (projectiveCodifferential V n a) +
      projectiveCodifferential V (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)) a = _
  rw [Form.Constructions.projectiveL2Pair_add_left]
  exact congrArg₂ (fun z w : ℂ => z + w)
    (projectiveCodifferential_pair_right V n (projectiveCodifferential V n a) a)
    (projectiveCodifferential_pair V (n + 1) a (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)).symm

end

/-! Harmonicity and energy for the genuine global Hodge Laplacian. -/

open scoped _root_.Manifold

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem projectiveL2Pair_self_re_nonpos (n : ℕ)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (ha : (Form.Constructions.projectiveL2Pair V n a a).re ≤ 0) : a = 0 := by
  apply Form.Constructions.smoothToProjectiveL2_injective V n
  rw [map_zero]
  apply (re_inner_self_nonpos (𝕜 := ℂ)).mp
  rw [Form.Constructions.smoothToProjectiveL2_inner]
  exact ha

variable (n : ℕ)

theorem projectivePositiveLaplacian_pair
    (a b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    Form.Constructions.projectiveL2Pair V (n + 1) (projectivePositiveLaplacian V n a) b =
      Form.Constructions.projectiveL2Pair V n (projectiveCodifferential V n a) (projectiveCodifferential V n b) +
        Form.Constructions.projectiveL2Pair V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b) := by
  change Form.Constructions.projectiveL2Pair V (n + 1)
    (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (projectiveCodifferential V n a) +
      projectiveCodifferential V (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)) b = _
  rw [Form.Constructions.projectiveL2Pair_add_left]
  exact congrArg₂ (fun z w : ℂ => z + w)
    (projectiveCodifferential_pair_right V n (projectiveCodifferential V n a) b)
    (projectiveCodifferential_pair V (n + 1) b (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)).symm

/-- A smooth form is harmonic exactly when it is closed and coclosed. -/
theorem projectivePositiveLaplacian_eq_zero_iff
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    projectivePositiveLaplacian V n a = 0 ↔
      DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0 ∧ projectiveCodifferential V n a = 0 := by
  constructor
  · intro ha
    have he := congrArg Complex.re (projectivePositiveLaplacian_energy V n a)
    rw [ha, projectiveL2Pair_zero_left, Complex.zero_re, Complex.add_re] at he
    have hδ := Form.Constructions.projectiveL2Pair_nonneg V n (projectiveCodifferential V n a)
    have hd := Form.Constructions.projectiveL2Pair_nonneg V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)
    constructor
    · apply projectiveL2Pair_self_re_nonpos V (n + 1 + 1)
      linarith
    · apply projectiveL2Pair_self_re_nonpos V n
      linarith
  · rintro ⟨hd, hδ⟩
    change DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (projectiveCodifferential V n a) +
      projectiveCodifferential V (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) = 0
    rw [hd, hδ, map_zero, map_zero, add_zero]

/-- The degree-zero Hodge Laplacian uses the same constructed adjoint. -/
def projectiveZeroLaplacian :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 →ₗ[ℂ]
      DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 :=
  (projectiveCodifferential V 0).comp DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d

theorem projectiveZeroLaplacian_eq_zero_iff
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
    projectiveZeroLaplacian V a = 0 ↔ DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0 := by
  constructor
  · intro ha
    apply projectiveL2Pair_self_re_nonpos V 1
    have h := projectiveCodifferential_pair V 0 a (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)
    change Form.Constructions.projectiveL2Pair V 1 (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) =
      Form.Constructions.projectiveL2Pair V 0 (projectiveZeroLaplacian V a) a at h
    rw [ha, projectiveL2Pair_zero_left] at h
    rw [h]
    exact le_rfl
  · intro ha
    change projectiveCodifferential V 0 (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) = 0
    rw [ha, map_zero]

/-- Exact and coclosed smooth forms vanish; thus harmonic representatives, when they exist, are unique. -/
theorem exact_coclosed_eq_zero
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (hab : DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b = a) (hδ : projectiveCodifferential V n a = 0) : a = 0 := by
  apply Form.Constructions.projectiveL2Pair_definite V (n + 1)
  have h := projectiveCodifferential_pair_right V n b a
  rw [hab, hδ, projectiveL2Pair_zero_right] at h
  exact h

/-- Coexact and closed smooth forms also vanish. -/
theorem coexact_closed_eq_zero
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (hab : projectiveCodifferential V n b = a) (hd : DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0) : a = 0 := by
  apply Form.Constructions.projectiveL2Pair_definite V n
  have h := projectiveCodifferential_pair V n a b
  rw [hab, hd, projectiveL2Pair_zero_right] at h
  exact h.symm

end

end OAI.Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions

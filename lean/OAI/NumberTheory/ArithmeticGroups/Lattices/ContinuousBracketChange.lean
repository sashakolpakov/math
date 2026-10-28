import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.AutomorphismTransversal

/-! # Continuous Bracket Change -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousBracketChange.Construction

noncomputable section

section

/-! Algebraic and continuous cochains agree in finite dimension,
with explicit linear equivalences preserving pointwise evaluation. -/

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

def finiteBilinearEquiv : (L →ₗ[ℝ] L →ₗ[ℝ] L) ≃ₗ[ℝ] (L →L[ℝ] L →L[ℝ] L) where
  toFun := Lie.AutomorphismTransversal.Construction.finiteContinuousBilinear
  invFun B := (ContinuousLinearMap.coeLM ℝ).comp B.toLinearMap
  left_inv B := by ext x y; rfl
  right_inv B := by ext x y; rfl
  map_add' B C := by ext x y; rfl
  map_smul' c B := by ext x y; rfl

theorem finiteBilinearEquiv_apply (B : L →ₗ[ℝ] L →ₗ[ℝ] L) (x y : L) :
    finiteBilinearEquiv B x y = B x y := rfl

theorem finiteBilinearEquiv_symm_apply (B : L →L[ℝ] L →L[ℝ] L) (x y : L) :
    finiteBilinearEquiv.symm B x y = B x y := rfl

def finiteTrilinearEquiv : (L →ₗ[ℝ] L →ₗ[ℝ] L →ₗ[ℝ] L) ≃ₗ[ℝ]
    (L →L[ℝ] L →L[ℝ] L →L[ℝ] L) where
  toFun B := (finiteBilinearEquiv.toLinearMap.comp B).toContinuousLinearMap
  invFun B := finiteBilinearEquiv.symm.toLinearMap.comp B.toLinearMap
  left_inv B := by ext x y z; rfl
  right_inv B := by ext x y z; rfl
  map_add' B C := by ext x y z; rfl
  map_smul' c B := by ext x y z; rfl

theorem finiteTrilinearEquiv_apply (B : L →ₗ[ℝ] L →ₗ[ℝ] L →ₗ[ℝ] L) (x y z : L) :
    finiteTrilinearEquiv B x y z = B x y z := rfl

theorem finiteTrilinearEquiv_symm_apply (B : L →L[ℝ] L →L[ℝ] L →L[ℝ] L) (x y z : L) :
    finiteTrilinearEquiv.symm B x y z = B x y z := rfl

def continuousBilinearOfFiniteDimensions
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] G) : E →L[ℝ] F →L[ℝ] G :=
  ((LinearMap.toContinuousLinearMap : (F →ₗ[ℝ] G) ≃ₗ[ℝ] (F →L[ℝ] G)).toLinearMap.comp
    B).toContinuousLinearMap

theorem continuousBilinearOfFiniteDimensions_apply
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] G) (x : E) (y : F) :
    continuousBilinearOfFiniteDimensions B x y = B x y := rfl

end

/-! Change of basis on continuous bilinear operations preserves
alternation and the Jacobi identity. -/

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]

def continuousBracketTransform (g h : L →L[ℝ] L) (B : L →L[ℝ] L →L[ℝ] L) :
    L →L[ℝ] L →L[ℝ] L :=
  (ContinuousLinearMap.compL ℝ L L L g).comp (((B.comp h).flip.comp h).flip)

theorem continuousBracketTransform_apply (g h : L →L[ℝ] L)
    (B : L →L[ℝ] L →L[ℝ] L) (x y : L) :
    continuousBracketTransform g h B x y = g (B (h x) (h y)) := rfl

def continuousBracketChange (e : L ≃L[ℝ] L) (B : L →L[ℝ] L →L[ℝ] L) :
    L →L[ℝ] L →L[ℝ] L := continuousBracketTransform e e.symm B

theorem continuousBracketChange_apply (e : L ≃L[ℝ] L)
    (B : L →L[ℝ] L →L[ℝ] L) (x y : L) :
    continuousBracketChange e B x y = e (B (e.symm x) (e.symm y)) := rfl

theorem continuousBracketChange_inverse (e : L ≃L[ℝ] L) (B : L →L[ℝ] L →L[ℝ] L) :
    continuousBracketChange e.symm (continuousBracketChange e B) = B := by
  ext x y
  simp only [continuousBracketChange_apply, ContinuousLinearEquiv.symm_symm,
    ContinuousLinearEquiv.symm_apply_apply]

def continuousBracketChangeEquiv (e : L ≃L[ℝ] L) :
    (L →L[ℝ] L →L[ℝ] L) ≃ₗ[ℝ] (L →L[ℝ] L →L[ℝ] L) where
  toFun := continuousBracketChange e
  invFun := continuousBracketChange e.symm
  left_inv := continuousBracketChange_inverse e
  right_inv B := by simpa only [ContinuousLinearEquiv.symm_symm] using continuousBracketChange_inverse e.symm B
  map_add' B C := by
    ext x y
    simp only [continuousBracketChange_apply, add_apply, map_add]
  map_smul' c B := by
    ext x y
    simp only [continuousBracketChange_apply, smul_apply, map_smul, RingHom.id_apply]

theorem continuousBracketChange_alternating (e : L ≃L[ℝ] L)
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ∀ x, B x x = 0) :
    ∀ x, continuousBracketChange e B x x = 0 := by
  intro x
  rw [continuousBracketChange_apply, hB, map_zero]

theorem continuousBracketChange_jacobi (e : L ≃L[ℝ] L)
    (B : L →L[ℝ] L →L[ℝ] L)
    (hB : ∀ x y z, B x (B y z) = B y (B x z) + B (B x y) z) :
    ∀ x y z, continuousBracketChange e B x (continuousBracketChange e B y z) =
      continuousBracketChange e B y (continuousBracketChange e B x z) +
      continuousBracketChange e B (continuousBracketChange e B x y) z := by
  intro x y z
  simp only [continuousBracketChange_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [hB, map_add]

theorem continuousBracketChange_jacobi_iff (e : L ≃L[ℝ] L) (B : L →L[ℝ] L →L[ℝ] L) :
    (∀ x y z, continuousBracketChange e B x (continuousBracketChange e B y z) =
      continuousBracketChange e B y (continuousBracketChange e B x z) +
      continuousBracketChange e B (continuousBracketChange e B x y) z) ↔
    ∀ x y z, B x (B y z) = B y (B x z) + B (B x y) z := by
  refine ⟨fun h => ?_, continuousBracketChange_jacobi e B⟩
  have h' := continuousBracketChange_jacobi e.symm (continuousBracketChange e B) h
  rwa [continuousBracketChange_inverse] at h'

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousBracketChange.Construction

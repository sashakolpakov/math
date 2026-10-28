import OAI.NumberTheory.ArithmeticGroups.Coordinates

/-! # Action -/

namespace OAI.NumberTheory.ArithmeticGroups.Action.CongruenceLevel

noncomputable section

open scoped Classical

section Descent
variable {K R Y T : Type*} [Field K] [Ring R]
  [AddCommGroup Y] [Module K Y] [AddCommGroup T] [Module K T]
  (π : Y →ₗ[K] T) (hs : Function.Surjective π)

def descendEnd (f : Module.End K Y) (hf : ∀ x, π x = 0 → π (f x) = 0) :
    Module.End K T :=
  ((π.ker).liftQ (π.comp f) hf).comp (π.quotKerEquivOfSurjective hs).symm.toLinearMap

lemma descendEnd_apply (f : Module.End K Y)
    (hf : ∀ x, π x = 0 → π (f x) = 0) (x : Y) :
    descendEnd π hs f hf (π x) = π (f x) := by
  simp [descendEnd, LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

def descendedAction (ρ : R →+* Module.End K Y)
    (hρ : ∀ a x, π x = 0 → π (ρ a x) = 0) : R →+* Module.End K T where
  toFun a := descendEnd π hs (ρ a) (hρ a)
  map_zero' := by
    ext t
    obtain ⟨x, rfl⟩ := hs t
    simp [descendEnd_apply]
  map_one' := by
    ext t
    obtain ⟨x, rfl⟩ := hs t
    simp [descendEnd_apply]
  map_add' a b := by
    ext t
    obtain ⟨x, rfl⟩ := hs t
    simp [descendEnd_apply]
  map_mul' a b := by
    ext t
    obtain ⟨x, rfl⟩ := hs t
    simp [Module.End.mul_apply, descendEnd_apply]

lemma descendedAction_apply (ρ : R →+* Module.End K Y)
    (hρ : ∀ a x, π x = 0 → π (ρ a x) = 0) (a : R) (x : Y) :
    descendedAction π hs ρ hρ a (π x) = π (ρ a x) := descendEnd_apply π hs _ _ x
end Descent

variable {E Place : Type*} [Field E] [Algebra ℚ E]
  (σ : Place → E →ₐ[ℚ] ℂ)

def ambientAction : E →+* Module.End ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient Place) where
  toFun a :=
    { toFun := fun u τ => (σ τ a • (u τ).1, AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ τ) a • (u τ).2)
      map_add' := fun u v => by ext τ j <;> simp <;> ring
      map_smul' := fun r u => by ext τ j <;> simp [smul_smul] <;> ring }
  map_zero' := by ext u τ j <;> simp
  map_one' := by ext u τ j <;> simp
  map_add' a b := by ext u τ j <;> simp [add_smul]
  map_mul' a b := by ext u τ j <;> simp [smul_smul]

lemma ambientAction_embedding (a : E) (x : Fin 3 → E) :
    ambientAction σ a (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x) = Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ (a • x) := by
  ext τ j <;> simp [ambientAction, Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates, map_mul]

lemma prescribed_action (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool)
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (a : E) (u : Geometry.ComplexBall.PrescribedSignsB.Ambient Place)
    (hu : Geometry.ComplexBall.PrescribedSignsB.Prescribed (fun τ x y => B τ x y) μ d z u) :
    Geometry.ComplexBall.PrescribedSignsB.Prescribed (fun τ x y => B τ x y) μ d z (ambientAction σ a u) := by
  intro τ
  have h := hu τ
  by_cases he : τ = μ
  · subst τ
    simp only at h ⊢
    refine ⟨(Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z}).smul_mem _ h.1, ?_⟩
    change B μ (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ μ) a • (u μ).2) = 0
    rw [map_smul, h.2, smul_zero]
  · simp only [ite_eq_right he] at h ⊢
    cases hd : d τ <;> simp only [hd, Bool.false_eq_true, ite_false, ite_true] at h ⊢
    · change AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ τ) a • (u τ).2 = 0
      rw [h, smul_zero]
    · change σ τ a • (u τ).1 = 0
      rw [h, smul_zero]

theorem quotient_integer_action
    [NumberField E]
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (P : Submodule ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient Place))
    (hP : ∀ u, u ∈ P ↔ Geometry.ComplexBall.PrescribedSignsB.Prescribed (fun τ x y => B τ x y) μ d z u)
    {T : Type*} [AddCommGroup T] [Module ℂ T]
    (π : Geometry.ComplexBall.PrescribedSignsB.Ambient Place →ₗ[ℂ] T) (hker : π.ker = P) (hs : Function.Surjective π) :
    ∃ ρ : NumberField.RingOfIntegers E →+* Module.End ℂ T,
      ∀ (a : NumberField.RingOfIntegers E) (x : Fin 3 → E),
        ρ a (π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x)) =
          π (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ ((a : E) • x)) := by
  let ρ₀ : NumberField.RingOfIntegers E →+* Module.End ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient Place) :=
    (ambientAction σ).comp (algebraMap (NumberField.RingOfIntegers E) E)
  have hρ : ∀ a u, π u = 0 → π (ρ₀ a u) = 0 := by
    intro a u hu
    have hp : u ∈ P := by rw [← hker]; exact hu
    have hpu := prescribed_action σ B μ d z (a : E) u ((hP u).mp hp)
    have hm : ρ₀ a u ∈ P := (hP _).mpr hpu
    rw [← hker] at hm
    exact hm
  refine ⟨descendedAction π hs ρ₀ hρ, ?_⟩
  intro a x
  rw [descendedAction_apply]
  change π (ambientAction σ (a : E) (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x)) = _
  rw [ambientAction_embedding]

end

end OAI.NumberTheory.ArithmeticGroups.Action.CongruenceLevel

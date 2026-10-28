import OAI.NumberTheory.ArithmeticGroups.Period
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace

/-! # Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Coordinates.CongruenceLevel

noncomputable section

open scoped Classical

open OAI.AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace

def ambientConjugation (Place : Type*) : Geometry.ComplexBall.PrescribedSignsB.Ambient Place ≃ₗ⋆[ℂ] Geometry.ComplexBall.PrescribedSignsB.Ambient Place where
  toFun := Geometry.ComplexBall.PrescribedSignsB.realConj
  invFun := Geometry.ComplexBall.PrescribedSignsB.realConj
  left_inv x := by ext τ j <;> simp [Geometry.ComplexBall.PrescribedSignsB.realConj]
  right_inv x := by ext τ j <;> simp [Geometry.ComplexBall.PrescribedSignsB.realConj]
  map_add' x y := by ext τ j <;> simp [Geometry.ComplexBall.PrescribedSignsB.realConj]
  map_smul' a x := by ext τ j <;> simp [Geometry.ComplexBall.PrescribedSignsB.realConj, star_smul]

lemma ambientConjugation_involutive (Place : Type*) :
    Function.Involutive (ambientConjugation Place) := by
  intro x
  exact (ambientConjugation Place).left_inv x

def realCoordinates (Place : Type*) : (Place → Geometry.ComplexBall.PrescribedSignsB.Vec) →ₗ[ℝ] Geometry.ComplexBall.PrescribedSignsB.Ambient Place where
  toFun x τ := (x τ, star (x τ))
  map_add' x y := by ext τ j <;> simp
  map_smul' a x := by ext τ j <;> simp

lemma realCoordinates_fixed (Place : Type*) (x : Place → Geometry.ComplexBall.PrescribedSignsB.Vec) :
    ambientConjugation Place (realCoordinates Place x) = realCoordinates Place x := by
  ext τ j <;> simp [ambientConjugation, Geometry.ComplexBall.PrescribedSignsB.realConj, realCoordinates]

lemma realCoordinates_injective (Place : Type*) :
    Function.Injective (realCoordinates Place) := by
  intro x y h
  funext τ
  exact congrArg (fun z : Geometry.ComplexBall.PrescribedSignsB.Ambient Place => (z τ).1) h

lemma realCoordinates_surjective_fixed (Place : Type*) (u : Geometry.ComplexBall.PrescribedSignsB.Ambient Place)
    (hu : ambientConjugation Place u = u) :
    ∃ x, realCoordinates Place x = u := by
  refine ⟨fun τ => (u τ).1, ?_⟩
  ext τ j
  · rfl
  · have h := congrArg (fun z : Geometry.ComplexBall.PrescribedSignsB.Ambient Place => (z τ).2 j) hu
    change star ((u τ).1 j) = (u τ).2 j at h
    change star ((u τ).1 j) = (u τ).2 j
    exact h

def complexTrace {Place : Type*} [Fintype Place]
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (t : Place → ℂ) : LinearMap.BilinForm ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient Place) :=
  ∑ τ, t τ •
    ((B τ).compl₁₂
      ((LinearMap.fst ℂ Geometry.ComplexBall.PrescribedSignsB.Vec Geometry.ComplexBall.PrescribedSignsB.Vec).comp (LinearMap.proj τ))
      ((LinearMap.snd ℂ Geometry.ComplexBall.PrescribedSignsB.Vec Geometry.ComplexBall.PrescribedSignsB.Vec).comp (LinearMap.proj τ)) -
    ((B τ).compl₁₂
      ((LinearMap.fst ℂ Geometry.ComplexBall.PrescribedSignsB.Vec Geometry.ComplexBall.PrescribedSignsB.Vec).comp (LinearMap.proj τ))
      ((LinearMap.snd ℂ Geometry.ComplexBall.PrescribedSignsB.Vec Geometry.ComplexBall.PrescribedSignsB.Vec).comp (LinearMap.proj τ))).flip)

lemma complexTrace_apply {Place : Type*} [Fintype Place]
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (t : Place → ℂ) (u v : Geometry.ComplexBall.PrescribedSignsB.Ambient Place) :
    complexTrace B t u v = Geometry.ComplexBall.PrescribedSignsB.tracePairing (fun τ x y => B τ x y) t u v := by
  simp [complexTrace, Geometry.ComplexBall.PrescribedSignsB.tracePairing]

lemma complexTrace_skew {Place : Type*} [Fintype Place]
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (t : Place → ℂ) (u v : Geometry.ComplexBall.PrescribedSignsB.Ambient Place) :
    complexTrace B t u v = -complexTrace B t v u := by
  simp only [complexTrace_apply, Geometry.ComplexBall.PrescribedSignsB.tracePairing, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro τ _
  ring

lemma complexTrace_real {Place : Type*} [Fintype Place]
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (hB : ∀ τ, Geometry.ComplexBall.PrescribedSignsB.HermitianB (B τ))
    (t : Place → ℂ) (ht : ∀ τ, star (t τ) = -t τ)
    (u v : Geometry.ComplexBall.PrescribedSignsB.Ambient Place) :
    star (complexTrace B t u v) =
      complexTrace B t (ambientConjugation Place u) (ambientConjugation Place v) := by
  simp only [complexTrace_apply, Geometry.ComplexBall.PrescribedSignsB.tracePairing, star_sum, star_mul, star_sub, ht]
  apply Finset.sum_congr rfl
  intro τ _
  rw [hB τ, hB τ]
  change _ = t τ * (B τ (star (u τ).2) (star (v τ).1) -
    B τ (star (v τ).2) (star (u τ).1))
  ring

lemma realCoordinates_projection_injective {Place : Type*} [Fintype Place]
    (r : ℕ) (Ψ : LinearMap.BilinForm ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient Place))
    (P : Submodule ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient Place))
    (hP : Geometry.ComplexBall.PrescribedSignsB.PositivePeriod r (fun x y => Ψ x y) (ambientConjugation Place) P)
    {T : Type*} [AddCommGroup T] [Module ℂ T]
    (π : Geometry.ComplexBall.PrescribedSignsB.Ambient Place →ₗ[ℂ] T) (hπ : π.ker = P) :
    Function.Injective ((π.restrictScalars ℝ).comp (realCoordinates Place)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hp : realCoordinates Place x ∈ P := by
    rw [← hπ]
    exact hx
  by_contra hn
  have hne : realCoordinates Place x ≠ 0 := by
    intro hz
    exact hn (realCoordinates_injective Place (hz.trans (map_zero _).symm))
  have hpos := (hP.2.2.2.1 _ hp hne).2
  rw [realCoordinates_fixed, hP.2.2.1 _ hp _ hp] at hpos
  simp at hpos

end

end OAI.NumberTheory.ArithmeticGroups.Coordinates.CongruenceLevel

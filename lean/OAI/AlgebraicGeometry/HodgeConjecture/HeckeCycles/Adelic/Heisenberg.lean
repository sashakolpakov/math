import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.FiniteOperators
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.Heisenberg
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierHeisenberg

/-! # Heisenberg -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Heisenberg.CM.Tensor

/-! The actual adelic Heisenberg formula factors into its real and
finite formulas on each pure Schwartz tensor. -/

open scoped Classical
variable {I : Type*} [Fintype I]

theorem phase_fst (p q x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    (∑ i, p i * (x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ (1 / 2) * q i)).1 =
      ∑ i, (p i).1 * ((x i).1 - algebraMap ℚ ℝ (1 / 2) * (q i).1) := by
  change (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (∑ i, p i * (x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ (1 / 2) * q i)) = _
  rw [map_sum]
  rfl

theorem phase_snd (p q x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    (∑ i, p i * (x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ (1 / 2) * q i)).2 =
      ∑ i, (p i).2 * ((x i).2 - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * (q i).2) := by
  change (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (∑ i, p i * (x i - algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ (1 / 2) * q i)) = _
  rw [map_sum]
  rfl

theorem function_tensor (p q x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (f : (I → ℝ) → ℂ) (φ : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) → ℂ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.character p q
      (fun y => f (fun i => (y i).1) * φ (fun i => (y i).2)) x =
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (fun i => (p i).1) (fun i => (q i).1) f (fun i => (x i).1) *
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.Finite.character (fun i => (p i).2) (fun i => (q i).2) φ
      (fun i => (x i).2) := by
  simp only [RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg, Constructed.AdelicCharacter.CM.character_apply, phase_fst, phase_snd]
  change (_ * _) * (f (fun i => (x i).1 - (q i).1) * φ (fun i => (x i).2 - (q i).2)) = _
  ring

theorem tensor_formula (n : ℕ) (p q : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.character p q (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ).val =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.pureTensor
        (Real.Heisenberg.CM.operator n (fun i => (p i).1) (fun i => (q i).1) f)
        (Finite.FourierHeisenberg.CM.operator (fun i => (p i).2) (fun i => (q i).2) φ) := by
  funext x
  exact function_tensor p q x f.val φ.val

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Heisenberg.CM.Tensor

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Heisenberg.CM

/-! Actual adelic Heisenberg operators preserve the full Schwartz
space defined as a finite span of real–finite tensors. -/

open scoped Classical
variable (n : ℕ)

def raw (p q : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n) →ₗ[ℂ] ((Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) → ℂ) where
  toFun f := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.character p q f.val
  map_add' f h := by
    funext x
    exact mul_add _ _ _
  map_smul' c f := by
    funext x
    exact mul_left_comm _ _ _

theorem raw_tensor (p q : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :
    raw n p q (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.pureTensor
      (Real.Heisenberg.CM.operator n (fun i => (p i).1) (fun i => (q i).1) f)
      (Finite.FourierHeisenberg.CM.operator (fun i => (p i).2) (fun i => (q i).2) φ) :=
  Tensor.tensor_formula n p q f φ

theorem raw_mem (p q : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) : raw n p q F ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n) := by
  obtain ⟨F, hF⟩ := F
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨f, φ, rfl⟩ := hF
    change raw n p q (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) ∈ _
    rw [raw_tensor]
    exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor _ _).property
  | zero =>
    change raw n p q 0 ∈ _
    rw [map_zero]
    exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)).zero_mem
  | add F G hF hG ihF ihG =>
    change raw n p q (⟨F, hF⟩ + ⟨G, hG⟩) ∈ _
    rw [map_add]
    exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)).add_mem ihF ihG
  | smul c F hF ih =>
    change raw n p q (c • ⟨F, hF⟩) ∈ _
    rw [map_smul]
    exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)).smul_mem c ih

def operator (p q : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n) →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n) :=
  (raw n p q).codRestrict (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) (raw_mem n p q)

theorem operator_apply (p q : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) (x : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    (operator n p q F).val x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg Constructed.AdelicCharacter.CM.character p q F.val x := rfl

theorem operator_tensor (p q : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :
    operator n p q (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor
      (Real.Heisenberg.CM.operator n (fun i => (p i).1) (fun i => (q i).1) f)
      (Finite.FourierHeisenberg.CM.operator (fun i => (p i).2) (fun i => (q i).2) φ) :=
  Subtype.ext (raw_tensor n p q f φ)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Heisenberg.CM

end

end OAI

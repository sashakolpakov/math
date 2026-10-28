import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.GraphSequence
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.RingHom.Flat

/-! # Diagonal Parameters -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DiagonalParameters

noncomputable section

/-! A flat polynomial presentation supplies the actual diagonal
parameters. Their images form a regular sequence at every local point
containing them. This applies to the etale charts of a smooth scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u

open _root_.MvPolynomial RingTheory.Sequence

variable (K A : Type u) [CommRing K] [CommRing A] [Algebra K A]
  (σ : Type) (f : MvPolynomial σ K →ₐ[K] A)

def chart : MvPolynomial σ A →ₐ[A] A ⊗[K] A :=
  (Algebra.TensorProduct.lTensor A f).comp (algebraTensorAlgEquiv K A).symm.toAlgHom

theorem chart_X (i : σ) : chart K A σ f (X i) = 1 ⊗ₜ[K] f (X i) := by
  simp [chart]

theorem chart_C (a : A) : chart K A σ f (C a) = a ⊗ₜ[K] 1 :=
  (chart K A σ f).commutes a

def parameter (i : σ) : A ⊗[K] A := 1 ⊗ₜ[K] f (X i) - f (X i) ⊗ₜ[K] 1

theorem chart_graph (i : σ) : chart K A σ f (X i - C (f (X i))) = parameter K A σ f i := by
  rw [map_sub, chart_X, chart_C]
  rfl

theorem flat (hf : f.Flat) : (chart K A σ f).Flat :=
  RingHom.Flat.comp (.of_bijective (algebraTensorAlgEquiv K A).symm.bijective) (hf.lTensor A)

theorem regular (hf : f.Flat) (B : Type u) [CommRing B] [IsLocalRing B]
    (g : A ⊗[K] A →+* B) (hg : g.Flat) (xs : List σ) (hx : xs.Nodup)
    (hm : ∀ i ∈ xs, g (parameter K A σ f i) ∈ IsLocalRing.maximalIdeal B) :
    IsRegular B (xs.map fun i => g (parameter K A σ f i)) := by
  let φ := g.comp (chart K A σ f).toRingHom
  let := φ.toAlgebra
  let : Module.Flat (MvPolynomial σ A) B := RingHom.flat_algebraMap_iff.mp
    (show φ.Flat from (flat K A σ f hf).comp hg)
  have h := Regular.SequenceFlatBaseChange.regular (MvPolynomial σ A) B
    (xs.map fun i => X i - C (f (X i)))
    (Polynomial.GraphSequence.weakly_regular A σ (fun i => f (X i)) xs hx) (by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      change g (chart K A σ f (X i - C (f (X i)))) ∈ IsLocalRing.maximalIdeal B
      rw [chart_graph]
      exact hm i hi)
  have he : (xs.map fun i => X i - C (f (X i))).map (algebraMap (MvPolynomial σ A) B) =
      xs.map (fun i => g (parameter K A σ f i)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    change g (chart K A σ f (X i - C (f (X i)))) = g (parameter K A σ f i)
    rw [chart_graph]
  exact he ▸ h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DiagonalParameters

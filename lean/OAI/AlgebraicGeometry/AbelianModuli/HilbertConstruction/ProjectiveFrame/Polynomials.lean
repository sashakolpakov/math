import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Discriminant
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Polynomials -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Polynomials

noncomputable section

/-! The labeled frame discriminant is a universal polynomial. Evaluation
and arbitrary ring base change preserve its actual determinant formula. -/
open scoped BigOperators Classical
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] {r m : ℕ}

def vectorFrameDiscriminant (b : Fin r → Fin r → R) (v : Fin r → R) : R :=
  Discriminant.projectiveFrameDiscriminant (Pi.basisFun R (Fin r)) b v

theorem vectorFrameDiscriminant_map (φ : R →+* A)
    (b : Fin r → Fin r → R) (v : Fin r → R) :
    φ (vectorFrameDiscriminant b v) =
      vectorFrameDiscriminant (fun i j => φ (b i j)) (fun j => φ (v j)) := by
  let : DecidableEq (Fin r) := Classical.decEq _
  have hd (b : Fin r → Fin r → R) :
      φ ((Pi.basisFun R (Fin r)).det b) =
        (Pi.basisFun A (Fin r)).det (fun i j => φ (b i j)) := by
    rw [Pi.basisFun_det_apply, Pi.basisFun_det_apply, φ.map_det]
    rfl
  have hu (i : Fin r) : (fun j k => φ (Function.update b i v j k)) =
      Function.update (fun j k => φ (b j k)) i (fun k => φ (v k)) := by
    funext j k
    by_cases hji : j = i
    · subst j
      simp [Function.update]
    · simp [Function.update, hji]
  simp only [vectorFrameDiscriminant, Discriminant.projectiveFrameDiscriminant, map_mul, map_prod]
  apply congrArg₂ (fun x y : A => x * y)
  · exact hd b
  · apply Finset.prod_congr rfl
    intro i _
    exact (hd (Function.update b i v)).trans (congrArg (Pi.basisFun A (Fin r)).det (hu i))

def labeledFrameDiscriminant (σ : Fin r → Fin m) (j : Fin m) (v : Fin m → Fin r → R) : R :=
  vectorFrameDiscriminant (fun i => v (σ i)) (v j)

def labeledFramePolynomial (R : Type u) [CommRing R]
    (σ : Fin r → Fin m) (j : Fin m) : MvPolynomial (Fin m × Fin r) R :=
  labeledFrameDiscriminant σ j (fun i k => MvPolynomial.X (i, k))

theorem labeledFramePolynomial_eval [Algebra R A]
    (σ : Fin r → Fin m) (j : Fin m) (v : Fin m → Fin r → A) :
    MvPolynomial.aeval (fun ik : Fin m × Fin r => v ik.1 ik.2) (labeledFramePolynomial R σ j) =
      labeledFrameDiscriminant σ j v := by
  unfold labeledFramePolynomial labeledFrameDiscriminant
  change (MvPolynomial.aeval (fun ik : Fin m × Fin r => v ik.1 ik.2)).toRingHom
    (vectorFrameDiscriminant (fun i k => MvPolynomial.X (σ i, k)) (fun k => MvPolynomial.X (j, k))) = _
  rw [vectorFrameDiscriminant_map]
  congr 1
  · funext i k
    exact MvPolynomial.aeval_X (fun ik : Fin m × Fin r => v ik.1 ik.2) (σ i, k)
  · funext k
    exact MvPolynomial.aeval_X (fun ik : Fin m × Fin r => v ik.1 ik.2) (j, k)

theorem labeledFramePolynomial_isUnit_iff [Algebra R A]
    (σ : Fin r → Fin m) (j : Fin m) (φ : MvPolynomial (Fin m × Fin r) R →ₐ[R] A) :
    IsUnit (φ (labeledFramePolynomial R σ j)) ↔
      ∃ b : Module.Basis (Fin r) A (Fin r → A),
        (∀ i k, b i k = φ (MvPolynomial.X (σ i, k))) ∧
        ∀ i, IsUnit (b.repr (fun k => φ (MvPolynomial.X (j, k))) i) := by
  unfold labeledFramePolynomial labeledFrameDiscriminant
  change IsUnit (φ.toRingHom
    (vectorFrameDiscriminant (fun i k => MvPolynomial.X (σ i, k)) (fun k => MvPolynomial.X (j, k)))) ↔ _
  rw [vectorFrameDiscriminant_map]
  change IsUnit (Discriminant.projectiveFrameDiscriminant (Pi.basisFun A (Fin r)) _ _) ↔ _
  rw [Discriminant.projectiveFrameDiscriminant_isUnit_iff]
  constructor
  · rintro ⟨b, hb, hu⟩
    exact ⟨b, fun i k => congrFun (hb i) k, hu⟩
  · rintro ⟨b, hb, hu⟩
    exact ⟨b, fun i => funext (hb i), hu⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Polynomials

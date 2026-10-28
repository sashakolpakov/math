import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodMatrixFamilies
import OAI.RepresentationTheory.Hecke.RadialDilation.GeometricTheta

/-! # Frame Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FrameProjection.Multiplicity

noncomputable section

section

/-! The actual frame-gradient projection as a continuous linear cotangent
map, with holomorphic dependence on an invertible frame matrix. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.GeometricTheta.Realization
open scoped Classical _root_.Matrix

def coordinateCovector : (Fin 2 → ℂ) →ₗ[ℂ] RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent where
  toFun a := ∑ i, a i • (ContinuousLinearMap.proj i : RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent)
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro x
    simp [add_mul]
    ring
  map_smul' c a := by
    apply ContinuousLinearMap.ext
    intro x
    simp [mul_assoc]

theorem coordinateCovector_apply (a x : Fin 2 → ℂ) :
    coordinateCovector a x = ∑ i, a i * x i := by
  simp [coordinateCovector]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def gradientLinear : ((ι → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun := RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradientVector
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def selectFrameCoordinates (j : Fin 2 → ι) : (ι → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun a := a ∘ j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def matrixProjection (j : Fin 2 → ι) :
    Matrix ι ι ℂ →ₗ[ℂ] (((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) where
  toFun A := (coordinateCovector.comp
    ((selectFrameCoordinates j).comp (A.mulVecLin.comp gradientLinear))).toContinuousLinearMap
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro l
    change coordinateCovector ((selectFrameCoordinates j) ((A + B) *ᵥ RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradientVector l)) = _
    simp only [Matrix.add_mulVec, map_add, add_apply]
    rfl
  map_smul' c A := by
    apply ContinuousLinearMap.ext
    intro l
    change coordinateCovector ((selectFrameCoordinates j) ((c • A) *ᵥ RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradientVector l)) = _
    simp only [Matrix.smul_mulVec, map_smul, smul_apply, RingHom.id_apply]
    rfl

def frameProjection (j : Fin 2 → ι) (Q : Matrix ι ι ℂ) :
    ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent := matrixProjection j Q⁻¹

theorem frameProjection_apply (j : Fin 2 → ι) (Q : Matrix ι ι ℂ)
    (l : (ι → ℂ) →L[ℂ] ℂ) :
    frameProjection j Q l = coordinateCovector (fun i => RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.frameGradient Q l (j i)) := rfl

theorem frameProjection_differentiable {O : Set RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates}
    (j : Fin 2 → ι) (Q : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates → Matrix ι ι ℂ)
    (hQ : DifferentiableOn ℂ Q O) (hdet : ∀ z ∈ O, (Q z).det ≠ 0) :
    DifferentiableOn ℂ (fun z => frameProjection j (Q z)) O := by
  have hi : DifferentiableOn ℂ (fun z => (Q z)⁻¹) O :=
    PeriodMatrixFamilies.Multiplicity.matrix_family_inverse_differentiable hQ hdet
  let f : (ι → ι → ℂ) →ₗ[ℂ] (((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) := matrixProjection j
  let fc : (ι → ι → ℂ) →L[ℂ] (((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) :=
    LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ι → ι → ℂ)
      (F' := (((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent)) f
  have hf : Differentiable ℂ fc := ContinuousLinearMap.differentiable
    (𝕜 := ℂ) (E := ι → ι → ℂ) (F := (((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent)) fc
  exact Differentiable.comp_differentiableOn (𝕜 := ℂ) (E := RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates)
    (F := ι → ι → ℂ) (G := (((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent)) hf hi

end

/-! The actual frame-gradient projection is onto the ball cotangent. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.GeometricTheta.Realization

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def vectorCovectorEquiv : (ι → ℂ) ≃ₗ[ℂ] ((ι → ℂ) →L[ℂ] ℂ) where
  toFun a := ∑ i, a i • (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)
  invFun := RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradientVector
  left_inv a := by
    funext i
    simp [RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradientVector, Pi.single_apply]
  right_inv l := by
    apply ContinuousLinearMap.ext
    intro x
    rw [RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.cotangent_expansion l x]
    simp [mul_comm]
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro x
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    apply ContinuousLinearMap.ext
    intro x
    simp [Finset.mul_sum, mul_assoc]

theorem frameGradient_surjective (Q : Matrix ι ι ℂ) (hQ : Q.det ≠ 0) :
    Function.Surjective (RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.frameGradient Q) := by
  intro u
  refine ⟨vectorCovectorEquiv (Q.mulVec u), ?_⟩
  change Q⁻¹ *ᵥ (vectorCovectorEquiv.symm (vectorCovectorEquiv (Q.mulVec u))) = u
  rw [LinearEquiv.symm_apply_apply, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hQ), Matrix.one_mulVec]

theorem frameProjection_surjective (j : Fin 2 → ι) (hj : Function.Injective j)
    (Q : Matrix ι ι ℂ) (hQ : Q.det ≠ 0) : Function.Surjective (frameProjection j Q) := by
  intro l
  obtain ⟨a, ha⟩ := (vectorCovectorEquiv (ι := Fin 2)).surjective l
  obtain ⟨b, hb⟩ := frameGradient_surjective Q hQ (Function.extend j a 0)
  refine ⟨b, ?_⟩
  rw [frameProjection_apply, hb]
  have he : (fun i => Function.extend j a 0 (j i)) = a :=
    funext (fun i => hj.extend_apply a 0 i)
  rw [he]
  exact ha

theorem scaled_frameProjection_surjective (j : Fin 2 → ι) (hj : Function.Injective j)
    (Q : Matrix ι ι ℂ) (hQ : Q.det ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    Function.Surjective (c • frameProjection j Q) :=
  (LinearEquiv.smulOfNeZero ℂ RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent c hc).surjective.comp
    (frameProjection_surjective j hj Q hQ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FrameProjection.Multiplicity

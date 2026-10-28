import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TracePhase

/-! # Ring Symplectic Pairing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RingSymplecticPairing.CM

noncomputable section

/-! Symplectic matrices over a commutative topological ring act by
continuous linear equivalences preserving the explicit alternating form. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TracePhase.CM

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

theorem pairing_negJ (x y : (I ⊕ I) → R) : Finite.TracePhase.CM.pairing x y = -(Matrix.J I R).toBilin' x y := by
  simp [Finite.TracePhase.CM.pairing, Matrix.toBilin'_apply, Matrix.J, Fintype.sum_sum_type,
    Matrix.fromBlocks, Matrix.one_apply, Finset.sum_sub_distrib, mul_comm]
  ring

theorem preserves (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I R) (x y : (I ⊕ I) → R) :
    Finite.TracePhase.CM.pairing (g.val *ᵥ x) (g.val *ᵥ y) = Finite.TracePhase.CM.pairing x y := by
  rw [pairing_negJ, pairing_negJ]
  have h := congrArg Matrix.toBilin' (SymplecticGroup.mem_iff'.mp g.property)
  rw [← Matrix.toBilin'_comp] at h
  exact congrArg Neg.neg (congrArg (fun B : LinearMap.BilinForm R ((I ⊕ I) → R) => B x y) h)

theorem matrix_symplectic (T : Matrix (I ⊕ I) (I ⊕ I) R)
    (hT : ∀ x y, Finite.TracePhase.CM.pairing (T *ᵥ x) (T *ᵥ y) = Finite.TracePhase.CM.pairing x y) :
    T ∈ Matrix.symplecticGroup I R := by
  apply SymplecticGroup.mem_iff'.mpr
  apply Matrix.toBilin'.injective
  rw [← Matrix.toBilin'_comp]
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change (Matrix.J I R).toBilin' (T *ᵥ x) (T *ᵥ y) = (Matrix.J I R).toBilin' x y
  have h := congrArg Neg.neg (hT x y)
  simpa only [pairing_negJ, neg_neg] using h

def linearEquiv (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I R) : ((I ⊕ I) → R) ≃ₗ[R] ((I ⊕ I) → R) where
  toFun := g.val.mulVec
  invFun := (g⁻¹).val.mulVec
  left_inv x := by
    rw [Matrix.mulVec_mulVec]
    have h : (g⁻¹).val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
    rw [h, Matrix.one_mulVec]
  right_inv x := by
    rw [Matrix.mulVec_mulVec]
    have h : g.val * (g⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel g)
    rw [h, Matrix.one_mulVec]
  map_add' := Matrix.mulVec_add g.val
  map_smul' := Matrix.mulVec_smul g.val

variable [TopologicalSpace R] [IsTopologicalRing R]

def continuousLinearEquiv (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I R) : ((I ⊕ I) → R) ≃L[R] ((I ⊕ I) → R) where
  toLinearEquiv := linearEquiv g
  continuous_toFun := by
    apply continuous_pi
    intro i
    change Continuous (fun x : (I ⊕ I) → R => ∑ j, g.val i j * x j)
    fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    change Continuous (fun x : (I ⊕ I) → R => ∑ j, (g⁻¹).val i j * x j)
    fun_prop

def rationalContinuousLinearEquiv [Module ℚ R] (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I R) :
    ((I ⊕ I) → R) ≃L[ℚ] ((I ⊕ I) → R) where
  toLinearEquiv :=
    { toAddEquiv := (linearEquiv g).toAddEquiv
      map_smul' := map_rat_smul (linearEquiv g).toAddEquiv }
  continuous_toFun := (continuousLinearEquiv g).continuous
  continuous_invFun := (continuousLinearEquiv g).symm.continuous

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RingSymplecticPairing.CM

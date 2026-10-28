import OAI.RepresentationTheory.Theta.Kernel.IntrinsicGraphProjector

/-! # Intrinsic Position Fixed Shear -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionFixedShear.Intrinsic

noncomputable section

/-! A symplectic linear map fixing positions is an actual symmetric
quadratic shear. This identifies its explicit Schwartz multiplier. -/

open scoped Classical _root_.Matrix

open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGraphProjector.Intrinsic

variable {I k : Type} [Fintype I] [DecidableEq I] [Field k]

def momentumOnPositions (E : ((I ⊕ I) → k) →ₗ[k] ((I ⊕ I) → k)) : (I → k) →ₗ[k] (I → k) where
  toFun q i := E (Sum.elim q (0 : I → k)) (.inr i)
  map_add' q r := by
    have he : Sum.elim (q + r) (0 : I → k) = Sum.elim q (0 : I → k) + Sum.elim r (0 : I → k) := by
      funext i
      cases i <;> simp
    rw [he,map_add]
    rfl
  map_smul' c q := by
    have he : Sum.elim (c • q) (0 : I → k) = c • Sum.elim q (0 : I → k) := by
      funext i
      cases i <;> simp
    rw [he,map_smul]
    rfl

def shearMatrix (E : ((I ⊕ I) → k) →ₗ[k] ((I ⊕ I) → k)) : Matrix I I k :=
  LinearMap.toMatrix' (momentumOnPositions E)

theorem shear_matrix_apply (E : ((I ⊕ I) → k) →ₗ[k] ((I ⊕ I) → k)) (q : I → k) :
    (shearMatrix E).mulVec q = fun i => E (Sum.elim q (0 : I → k)) (.inr i) :=
  LinearMap.toMatrix'_mulVec _ q

theorem position_fixed_momenta (E : ((I ⊕ I) → k) →ₗ[k] ((I ⊕ I) → k))
    (hE : ∀ x y, IntrinsicGraphProjector.Intrinsic.phasePairing (E x) (E y) = IntrinsicGraphProjector.Intrinsic.phasePairing x y)
    (hpos : ∀ x i, E x (.inl i) = x (.inl i)) (p : I → k) :
    E (Sum.elim (0 : I → k) p) = Sum.elim (0 : I → k) p := by
  funext i
  cases i with
  | inl i => exact hpos _ i
  | inr i =>
    have he := hE (Sum.elim (0 : I → k) p) (Sum.elim (Pi.single i 1) (0 : I → k))
    have hzero : (fun j => E (Sum.elim (0 : I → k) p) (.inl j)) = (0 : I → k) := funext (hpos _)
    have hsingle : (fun j => E (Sum.elim (Pi.single i 1) (0 : I → k)) (.inl j)) = Pi.single i 1 :=
      funext (hpos _)
    change (fun j => E (Sum.elim (0 : I → k) p) (.inl j)) ⬝ᵥ
      (fun j => E (Sum.elim (Pi.single i 1) (0 : I → k)) (.inr j)) -
        (fun j => E (Sum.elim (0 : I → k) p) (.inr j)) ⬝ᵥ
          (fun j => E (Sum.elim (Pi.single i 1) (0 : I → k)) (.inl j)) =
      (0 : I → k) ⬝ᵥ (0 : I → k) - p ⬝ᵥ Pi.single i 1 at he
    rw [hzero,hsingle,zero_dotProduct,zero_dotProduct,dotProduct_single,dotProduct_single,
      mul_one,mul_one,zero_sub,zero_sub] at he
    exact neg_injective he

theorem position_fixed_formula (E : ((I ⊕ I) → k) →ₗ[k] ((I ⊕ I) → k))
    (hE : ∀ x y, IntrinsicGraphProjector.Intrinsic.phasePairing (E x) (E y) = IntrinsicGraphProjector.Intrinsic.phasePairing x y)
    (hpos : ∀ x i, E x (.inl i) = x (.inl i)) (x : (I ⊕ I) → k) :
    E x = Sum.elim (fun i => x (.inl i))
      ((fun i => x (.inr i)) + (shearMatrix E).mulVec (fun i => x (.inl i))) := by
  have hx : x = Sum.elim (fun i => x (.inl i)) (0 : I → k) +
      Sum.elim (0 : I → k) (fun i => x (.inr i)) := by
    funext i
    cases i <;> simp
  have he := (congrArg E hx).trans (E.map_add _ _)
  rw [he,position_fixed_momenta E hE hpos,shear_matrix_apply]
  funext i
  cases i with
  | inl i => simpa using hpos (Sum.elim (fun i => x (.inl i)) (0 : I → k)) i
  | inr i => exact add_comm _ _

theorem shear_matrix_symmetric (E : ((I ⊕ I) → k) →ₗ[k] ((I ⊕ I) → k))
    (hE : ∀ x y, IntrinsicGraphProjector.Intrinsic.phasePairing (E x) (E y) = IntrinsicGraphProjector.Intrinsic.phasePairing x y)
    (hpos : ∀ x i, E x (.inl i) = x (.inl i)) : (shearMatrix E).IsSymm := by
  have hb (q r : I → k) : q ⬝ᵥ (shearMatrix E).mulVec r = r ⬝ᵥ (shearMatrix E).mulVec q := by
    have he := hE (Sum.elim q (0 : I → k)) (Sum.elim r (0 : I → k))
    rw [position_fixed_formula E hE hpos,position_fixed_formula E hE hpos] at he
    change q ⬝ᵥ ((0 : I → k) + (shearMatrix E).mulVec r) -
      ((0 : I → k) + (shearMatrix E).mulVec q) ⬝ᵥ r = q ⬝ᵥ (0 : I → k) - (0 : I → k) ⬝ᵥ r at he
    rw [zero_add,zero_add,dotProduct_zero,zero_dotProduct,sub_self,dotProduct_comm _ r] at he
    exact sub_eq_zero.mp he
  change (shearMatrix E)ᵀ = shearMatrix E
  ext i j
  have he := hb (Pi.single j 1) (Pi.single i 1)
  rw [single_dotProduct,single_dotProduct,one_mul,one_mul,Matrix.mulVec_single,Matrix.mulVec_single] at he
  simp only [MulOpposite.op_one,one_smul] at he
  exact he

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionFixedShear.Intrinsic

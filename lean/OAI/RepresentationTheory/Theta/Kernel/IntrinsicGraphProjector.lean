import Mathlib

/-! # Intrinsic Graph Projector -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicGraphProjector.Intrinsic

noncomputable section

/-! A self-adjoint phase-space projector preserving a Gaussian graph
is the cotangent projector when the quadratic form splits along its
position projector. -/

open scoped Classical _root_.Matrix

variable {I k : Type} [Fintype I] [DecidableEq I] [Field k]

def phasePairing (x y : (I ⊕ I) → k) : k :=
  (fun i => x (.inl i)) ⬝ᵥ (fun i => y (.inr i)) -
    (fun i => x (.inr i)) ⬝ᵥ (fun i => y (.inl i))

theorem projector_on_momenta (E : ((I ⊕ I) → k) →ₗ[k] ((I ⊕ I) → k))
    (S : Matrix I I k)
    (hE : ∀ x y, phasePairing (E x) y = phasePairing x (E y))
    (hpos : ∀ x i, E x (.inl i) = S.mulVec (fun j => x (.inl j)) i)
    (p : I → k) : E (Sum.elim (0 : I → k) p) = Sum.elim (0 : I → k) (Sᵀ.mulVec p) := by
  funext i
  cases i with
  | inl i =>
    rw [hpos]
    exact congrFun (Matrix.mulVec_zero S) i
  | inr i =>
    have he := hE (Sum.elim (0 : I → k) p) (Sum.elim (Pi.single i 1) (0 : I → k))
    change (fun j => E (Sum.elim (0 : I → k) p) (.inl j)) ⬝ᵥ (0 : I → k) -
      (fun j => E (Sum.elim (0 : I → k) p) (.inr j)) ⬝ᵥ Pi.single i 1 =
        (0 : I → k) ⬝ᵥ (fun j => E (Sum.elim (Pi.single i 1) (0 : I → k)) (.inr j)) -
          p ⬝ᵥ (fun j => E (Sum.elim (Pi.single i 1) (0 : I → k)) (.inl j)) at he
    simp only [zero_dotProduct,dotProduct_zero,zero_sub] at he
    have hq : (fun j => E (Sum.elim (Pi.single i 1) (0 : I → k)) (.inl j)) = S.mulVec (Pi.single i 1) :=
      funext (hpos (Sum.elim (Pi.single i 1) (0 : I → k)))
    rw [hq,← Matrix.dotProduct_transpose_mulVec S (Pi.single i 1) p,
      dotProduct_single,single_dotProduct,mul_one,one_mul] at he
    exact neg_injective he

theorem graph_projector_cotangent (E : ((I ⊕ I) → k) →ₗ[k] ((I ⊕ I) → k))
    (S Z : Matrix I I k)
    (hE : ∀ x y, phasePairing (E x) y = phasePairing x (E y))
    (hpos : ∀ x i, E x (.inl i) = S.mulVec (fun j => x (.inl j)) i)
    (hgraph : ∀ q, E (Sum.elim q (Z.mulVec q)) = Sum.elim (S.mulVec q) (Z.mulVec (S.mulVec q)))
    (hZS : Z * S = Sᵀ * Z) (x : (I ⊕ I) → k) :
    E x = Sum.elim (S.mulVec (fun i => x (.inl i))) (Sᵀ.mulVec (fun i => x (.inr i))) := by
  let q : I → k := fun i => x (.inl i)
  let p : I → k := fun i => x (.inr i)
  have hx : x = Sum.elim q (Z.mulVec q) + Sum.elim (0 : I → k) (p - Z.mulVec q) := by
    funext i
    cases i <;> simp [q,p]
  have hcomm : Z.mulVec (S.mulVec q) = Sᵀ.mulVec (Z.mulVec q) := by
    rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hZS]
  have he : E x = E (Sum.elim q (Z.mulVec q)) + E (Sum.elim (0 : I → k) (p - Z.mulVec q)) :=
    (congrArg E hx).trans (E.map_add _ _)
  rw [he,hgraph,projector_on_momenta E S hE hpos]
  funext i
  cases i with
  | inl i => simp [q,p]
  | inr i =>
    change Z.mulVec (S.mulVec q) i + Sᵀ.mulVec (p - Z.mulVec q) i = Sᵀ.mulVec p i
    rw [hcomm,Matrix.mulVec_sub]
    simp

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicGraphProjector.Intrinsic

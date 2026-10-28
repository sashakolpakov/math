import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.SquareZeroAlgebraComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorReductionEquiv

/-! # Dual Product Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualProductComparison

noncomputable section

/-! A smooth affine deformation over dual numbers is an actual product
with its identified smooth special fiber. The isomorphism retains the
original reduction map and the full dual-number base action. -/

open scoped TensorProduct

attribute [local irreducible] Dual.TensorReductionEquiv.dualScalarAlgebra Dual.TensorReductionEquiv.dualTensorReductionBaseEquiv
  Dual.TensorReductionEquiv.dualTensorReductionQuotientEquiv Dual.TensorReductionEquiv.dualTensorCanonicalReductionEquiv

variable {k A S : Type*} [CommRing k] [CommRing A] [CommRing S]
    [Algebra k A] [Algebra (DualNumber k) S]
    [Algebra.FormallySmooth k A] [Algebra.FormallySmooth (DualNumber k) S]

local instance : CommRing (DualNumber k ⊗[k] A) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := A)

theorem exists_smooth_dual_product_comparison (q : S →+* A)
    (hq : Function.Surjective q)
    (hker : RingHom.ker q = (Dual.TensorReduction.dualScalarReductionIdeal k).map (algebraMap (DualNumber k) S))
    (hbase : ∀ c : DualNumber k, q (algebraMap (DualNumber k) S c) = algebraMap k A c.fst) :
    ∃ f : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A),
      ∀ s, Dual.TensorReduction.dualTensorReduction k A (f s) = q s := by
  let := Dual.TensorReductionEquiv.dualScalarAlgebra k A
  let qR : S →ₐ[DualNumber k] A :=
    { q with commutes' := fun c => (hbase c).trans (Dual.TensorReductionEquiv.dualScalarAlgebra_map k A c).symm }
  let I := Dual.TensorReduction.dualScalarReductionIdeal k
  let J := I.map (algebraMap (DualNumber k) S)
  let K : Ideal (DualNumber k ⊗[k] A) :=
    I.map (algebraMap (DualNumber k) (DualNumber k ⊗[k] A))
  have hqR : Function.Surjective qR := hq
  have hkerR : RingHom.ker qR = J := hker
  let eS : (S ⧸ J) ≃ₐ[DualNumber k] A :=
    (Ideal.quotientEquivAlgOfEq (DualNumber k) hkerR.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hqR)
  let eD : ((DualNumber k ⊗[k] A) ⧸ K) ≃ₐ[DualNumber k] A :=
    Dual.TensorReductionEquiv.dualTensorCanonicalReductionEquiv k A
  have : Algebra.FormallySmooth (DualNumber k) (DualNumber k ⊗[k] A) := inferInstance
  obtain ⟨f, hf⟩ := SquareZeroAlgebraComparison.exists_smooth_algebraEquiv_lift_squareZero
    (R := DualNumber k) (S := S) (T := DualNumber k ⊗[k] A) I
    (Dual.TensorReduction.dualScalarReductionIdeal_square k) (eS.trans eD.symm)
  refine ⟨f, ?_⟩
  intro s
  have he := AlgHom.congr_fun hf s
  change Ideal.Quotient.mk K (f s) = eD.symm (eS (Ideal.Quotient.mk J s)) at he
  calc
    Dual.TensorReduction.dualTensorReduction k A (f s) = eD (Ideal.Quotient.mk K (f s)) :=
      (Dual.TensorReductionEquiv.dualTensorCanonicalReductionEquiv_mk k A (f s)).symm
    _ = eS (Ideal.Quotient.mk J s) :=
      (congrArg eD he).trans (eD.apply_symm_apply _)
    _ = q s := by
      dsimp only [eS]
      rw [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
        Ideal.quotientKerAlgEquivOfSurjective_mk]
      rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualProductComparison

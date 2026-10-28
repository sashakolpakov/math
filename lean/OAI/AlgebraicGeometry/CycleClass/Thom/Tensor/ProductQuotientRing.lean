import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalQuotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Product Quotient Ring -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductQuotientRing.Constructions

noncomputable section

/-! The quotient by the two extended ideals is the actual tensor
product of the two quotient algebras. The maps are induced by the
canonical quotient maps and the two tensor inclusions. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (k R S : Type u) [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
  (I : Ideal R) (J : Ideal S)

def leftFactor : R ⧸ I →ₐ[k] (R ⊗[k] S) ⧸ TorAlgebra.ExternalQuotient.productIdeal k R S I J :=
  Ideal.Quotient.liftₐ I
    ((Ideal.Quotient.mkₐ k (TorAlgebra.ExternalQuotient.productIdeal k R S I J)).comp Algebra.TensorProduct.includeLeft) (by
      intro r hr
      change Ideal.Quotient.mk (TorAlgebra.ExternalQuotient.productIdeal k R S I J) (r ⊗ₜ[k] 1) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hI : I.map (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := R) (B := S)).toRingHom ≤
          TorAlgebra.ExternalQuotient.productIdeal k R S I J := le_sup_right
      exact hI (Ideal.mem_map_of_mem _ hr))

def rightFactor : S ⧸ J →ₐ[k] (R ⊗[k] S) ⧸ TorAlgebra.ExternalQuotient.productIdeal k R S I J :=
  Ideal.Quotient.liftₐ J
    ((Ideal.Quotient.mkₐ k (TorAlgebra.ExternalQuotient.productIdeal k R S I J)).comp Algebra.TensorProduct.includeRight) (by
      intro s hs
      change Ideal.Quotient.mk (TorAlgebra.ExternalQuotient.productIdeal k R S I J) (1 ⊗ₜ[k] s) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hJ : J.map (Algebra.TensorProduct.includeRight (R := k) (A := R) (B := S)).toRingHom ≤
          TorAlgebra.ExternalQuotient.productIdeal k R S I J := le_sup_left
      exact hJ (Ideal.mem_map_of_mem _ hs))

def fromProduct : (R ⧸ I) ⊗[k] (S ⧸ J) →ₐ[k] (R ⊗[k] S) ⧸ TorAlgebra.ExternalQuotient.productIdeal k R S I J :=
  Algebra.TensorProduct.lift (leftFactor k R S I J) (rightFactor k R S I J) (fun _ _ => .all _ _)

def productMap : R ⊗[k] S →ₐ[k] (R ⧸ I) ⊗[k] (S ⧸ J) :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k J)

theorem productIdeal_le_ker : TorAlgebra.ExternalQuotient.productIdeal k R S I J ≤ RingHom.ker (productMap k R S I J).toRingHom := by
  apply sup_le
  · apply Ideal.map_le_iff_le_comap.mpr
    intro s hs
    change (1 : R ⧸ I) ⊗ₜ[k] Ideal.Quotient.mk J s = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hs, TensorProduct.tmul_zero]
  · apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change Ideal.Quotient.mk I r ⊗ₜ[k] (1 : S ⧸ J) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, TensorProduct.zero_tmul]

def toProduct : (R ⊗[k] S) ⧸ TorAlgebra.ExternalQuotient.productIdeal k R S I J →ₐ[k] (R ⧸ I) ⊗[k] (S ⧸ J) :=
  Ideal.Quotient.liftₐ (TorAlgebra.ExternalQuotient.productIdeal k R S I J) (productMap k R S I J) (productIdeal_le_ker k R S I J)

def quotientProductEquiv : ((R ⊗[k] S) ⧸ TorAlgebra.ExternalQuotient.productIdeal k R S I J) ≃ₐ[k] (R ⧸ I) ⊗[k] (S ⧸ J) :=
  AlgEquiv.ofAlgHom (toProduct k R S I J) (fromProduct k R S I J)
    (by
      apply Algebra.TensorProduct.ext
      · apply AlgHom.ext
        intro r
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        simp [toProduct, fromProduct, leftFactor, rightFactor, productMap]
      · apply AlgHom.ext
        intro s
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
        simp [toProduct, fromProduct, leftFactor, rightFactor, productMap])
    (by
      apply Ideal.Quotient.algHom_ext
      apply Algebra.TensorProduct.ext
      · ext r
        simp [toProduct, fromProduct, leftFactor, rightFactor, productMap]
      · ext s
        simp [toProduct, fromProduct, leftFactor, rightFactor, productMap])

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductQuotientRing.Constructions

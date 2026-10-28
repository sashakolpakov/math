import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.TensorMaps
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Flat.Basic

/-! # Transcendence Dimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.TranscendenceDimension.Constructions

noncomputable section

/-! Transcendence degrees of integral tensor products add. The proof uses
actual Noether normalization, injective tensor maps, and integral extensions. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Integral.TensorMaps.Constructions

theorem trdeg_eq_of_injective_integral {k P A : Type}
    [Field k] [CommRing P] [IsDomain P] [CommRing A] [IsDomain A]
    [Algebra k P] [Algebra k A] (f : P →ₐ[k] A)
    (hf : Function.Injective f) (hi : f.IsIntegral) :
    Algebra.trdeg k P = Algebra.trdeg k A := by
  let : Algebra P A := f.toRingHom.toAlgebra
  let : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hf
  let : IsScalarTower k P A := IsScalarTower.of_algHom f
  let : Algebra.IsIntegral P A := ⟨hi⟩
  have h := trdeg_add_eq k P (A := A)
  simpa only [trdeg_eq_zero, add_zero] using h

theorem tensorProduct_trdeg {k A B : Type} [Field k]
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra k A] [Algebra k B] [Algebra.FiniteType k A] [Algebra.FiniteType k B]
    [IsDomain (A ⊗[k] B)] :
    Algebra.trdeg k (A ⊗[k] B) = Algebra.trdeg k A + Algebra.trdeg k B := by
  obtain ⟨n, f, hfi, hf⟩ := exists_integral_inj_algHom_of_fg k A
  obtain ⟨m, g, hgi, hg⟩ := exists_integral_inj_algHom_of_fg k B
  let φ := Algebra.TensorProduct.map f g
  have hφ : Function.Injective φ :=
    TensorProduct.map_injective_of_flat_flat f.toLinearMap g.toLinearMap hfi hgi
  let : IsDomain (MvPolynomial (Fin n) k ⊗[k] MvPolynomial (Fin m) k) :=
    Function.Injective.isDomain φ hφ
  calc
    Algebra.trdeg k (A ⊗[k] B) =
        Algebra.trdeg k (MvPolynomial (Fin n) k ⊗[k] MvPolynomial (Fin m) k) :=
      (trdeg_eq_of_injective_integral φ hφ (Integral.TensorMaps.Constructions.tensorMap_isIntegral f g hf hg)).symm
    _ = Algebra.trdeg k (MvPolynomial (Fin n ⊕ Fin m) k) :=
      (MvPolynomial.tensorEquivSum k (Fin n) (Fin m) k).trdeg_eq
    _ = Algebra.trdeg k A + Algebra.trdeg k B := by
      rw [← trdeg_eq_of_injective_integral f hfi hf, ← trdeg_eq_of_injective_integral g hgi hg]
      simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_sum, Cardinal.lift_id]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.TranscendenceDimension.Constructions

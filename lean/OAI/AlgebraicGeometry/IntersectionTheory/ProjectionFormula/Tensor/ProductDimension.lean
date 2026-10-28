import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.AlgebraTranscendence
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Product Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ProductDimension

noncomputable section

section

/-! Prime quotients of tensor products of affine domains have
dimension at most the sum of the two factor dimensions. -/

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

theorem normalization (K A : Type) [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] :
    ∃ (r : ℕ) (g : MvPolynomial (Fin r) K →ₐ[K] A),
      Function.Injective g ∧ g.Finite ∧ Algebra.trdeg K A = r := by
  obtain ⟨r, g, hi, hf⟩ := exists_finite_inj_algHom_of_fg K A
  let := g.toRingHom.toAlgebra
  let : Module.Finite (MvPolynomial (Fin r) K) A := hf
  let : FaithfulSMul (MvPolynomial (Fin r) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hi
  let : IsScalarTower K (MvPolynomial (Fin r) K) A :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  have he := trdeg_add_eq K (MvPolynomial (Fin r) K) (A := A)
  rw [trdeg_eq_zero (R := MvPolynomial (Fin r) K) (A := A), add_zero] at he
  refine ⟨r, g, hi, hf, ?_⟩
  simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype,
    Fintype.card_fin, Cardinal.lift_natCast] using he.symm

theorem quotient (K A B : Type) [Field K] [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra K A] [Algebra K B]
    [Algebra.FiniteType K A] [Algebra.FiniteType K B]
    (Q : Ideal (A ⊗[K] B)) [Q.IsPrime] :
    Algebra.trdeg K ((A ⊗[K] B) ⧸ Q) ≤ Algebra.trdeg K A + Algebra.trdeg K B := by
  obtain ⟨r, f, _, hf, hr⟩ := normalization K A
  obtain ⟨s, g, _, hg, hs⟩ := normalization K B
  let e := MvPolynomial.tensorEquivSum K (Fin r) (Fin s) K
  let φ := (Algebra.TensorProduct.map f g).comp e.symm.toAlgHom
  have hφ : φ.Finite :=
    (RingHom.Finite.tensorProductMap hf hg).comp e.symm.toRingEquiv.finite
  let ψ := (Ideal.Quotient.mkₐ K Q).comp φ
  have hψ : ψ.Finite :=
    (RingHom.Finite.of_surjective (Ideal.Quotient.mk Q) (Ideal.Quotient.mk_surjective)).comp hφ
  have hd := ProjectionFormula.Finite.AlgebraTranscendence.polynomial ψ hψ
  simpa only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, hr, hs] using hd

theorem quotient_toNat (K A B : Type) [Field K] [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra K A] [Algebra K B]
    [Algebra.FiniteType K A] [Algebra.FiniteType K B]
    (Q : Ideal (A ⊗[K] B)) [Q.IsPrime] :
    (Algebra.trdeg K ((A ⊗[K] B) ⧸ Q)).toNat ≤
      (Algebra.trdeg K A).toNat + (Algebra.trdeg K B).toNat := by
  have hA := trdeg_lt_aleph0_of_finiteType (R := K) (S := A)
  have hB := trdeg_lt_aleph0_of_finiteType (R := K) (S := B)
  have h := Cardinal.toNat_le_toNat (quotient K A B Q) (Cardinal.add_lt_aleph0 hA hB)
  rwa [Cardinal.toNat_add hA hB] at h

end

/-! The dimension bound for an affine product descends through the
actual prime ideals in its two factors. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace Quotient

variable (K A B : Type) [Field K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]
  (p : Ideal A) (q : Ideal B) (Q : Ideal (A ⊗[K] B))
  (hp : p ≤ Q.comap (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B))
  (hq : q ≤ Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B))

def left : A ⧸ p →ₐ[K] (A ⊗[K] B) ⧸ Q :=
  Ideal.Quotient.liftₐ p
    ((Ideal.Quotient.mkₐ K Q).comp Algebra.TensorProduct.includeLeft)
    (fun _ ha => (Ideal.Quotient.eq_zero_iff_mem (I := Q)).mpr (hp ha))

def right : B ⧸ q →ₐ[K] (A ⊗[K] B) ⧸ Q :=
  Ideal.Quotient.liftₐ q
    ((Ideal.Quotient.mkₐ K Q).comp Algebra.TensorProduct.includeRight)
    (fun _ hb => (Ideal.Quotient.eq_zero_iff_mem (I := Q)).mpr (hq hb))

def map : (A ⧸ p) ⊗[K] (B ⧸ q) →ₐ[K] (A ⊗[K] B) ⧸ Q :=
  Algebra.TensorProduct.lift (left K A B p Q hp) (right K A B q Q hq)
    (fun _ _ => Commute.all _ _)

theorem map_tmul (a : A) (b : B) :
    ProductDimension.Quotient.map K A B p q Q hp hq ((Ideal.Quotient.mk p a) ⊗ₜ[K] (Ideal.Quotient.mk q b)) =
      Ideal.Quotient.mk Q (a ⊗ₜ[K] b) := by
  change Ideal.Quotient.mk Q (a ⊗ₜ[K] (1 : B)) *
    Ideal.Quotient.mk Q ((1 : A) ⊗ₜ[K] b) = _
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem surjective : Function.Surjective (ProductDimension.Quotient.map K A B p q Q hp hq) := by
  intro z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction z using TensorProduct.inductionOn with
  | tmul a b => exact ⟨_, map_tmul K A B p q Q hp hq a b⟩
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add, hx', hy', map_add]⟩

include hp hq in
theorem bound [Algebra.FiniteType K A] [Algebra.FiniteType K B]
    [p.IsPrime] [q.IsPrime] [Q.IsPrime] :
    (Algebra.trdeg K ((A ⊗[K] B) ⧸ Q)).toNat ≤
      (Algebra.trdeg K (A ⧸ p)).toNat + (Algebra.trdeg K (B ⧸ q)).toNat := by
  let f := ProductDimension.Quotient.map K A B p q Q hp hq
  let I := RingHom.ker f.toRingHom
  let : I.IsPrime := RingHom.ker_isPrime f.toRingHom
  let e : (((A ⧸ p) ⊗[K] (B ⧸ q)) ⧸ I) ≃ₐ[K] ((A ⊗[K] B) ⧸ Q) :=
    Ideal.quotientKerAlgEquivOfSurjective (surjective K A B p q Q hp hq)
  have he := AlgEquiv.trdeg_eq (R := K) (A := (((A ⧸ p) ⊗[K] (B ⧸ q)) ⧸ I)) e
  rw [← he]
  exact quotient_toNat K (A ⧸ p) (B ⧸ q) I

end Quotient

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ProductDimension

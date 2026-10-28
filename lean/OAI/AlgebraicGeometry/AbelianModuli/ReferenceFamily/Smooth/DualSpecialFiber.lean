import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.MappedQuotient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorReductionEquiv

/-! # Dual Special Fiber -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualSpecialFiber

noncomputable section

/-! The identified special fiber of an actual formally smooth dual-number
algebra is formally smooth over the original coefficient ring. -/

def dualScalarQuotientEquiv (k : Type*) [CommRing k] :
    ((DualNumber k) ⧸ Dual.TensorReduction.dualScalarReductionIdeal k) ≃ₐ[k] k :=
  Ideal.quotientKerAlgEquivOfSurjective (f := TrivSqZeroExt.fstHom k k k)
    (fun a => ⟨(a, 0), rfl⟩)

theorem dualScalarQuotientEquiv_mk (k : Type*) [CommRing k] (c : DualNumber k) :
    dualScalarQuotientEquiv k (Ideal.Quotient.mk (Dual.TensorReduction.dualScalarReductionIdeal k) c) = c.fst := rfl

variable {k A S : Type*} [CommRing k] [CommRing A] [CommRing S]
    [Algebra k A] [Algebra (DualNumber k) S] [Algebra.FormallySmooth (DualNumber k) S]

theorem formallySmooth_dual_specialFiber (q : S →+* A) (hq : Function.Surjective q)
    (hker : RingHom.ker q = (Dual.TensorReduction.dualScalarReductionIdeal k).map (algebraMap (DualNumber k) S))
    (hbase : ∀ c : DualNumber k, q (algebraMap (DualNumber k) S c) = algebraMap k A c.fst) :
    Algebra.FormallySmooth k A := by
  let : Algebra k S := ((algebraMap (DualNumber k) S).comp (algebraMap k (DualNumber k))).toAlgebra
  let : IsScalarTower k (DualNumber k) S :=
    IsScalarTower.of_algebraMap_eq' (R := k) (S := DualNumber k) (A := S) rfl
  let I := Dual.TensorReduction.dualScalarReductionIdeal k
  let J := I.map (algebraMap (DualNumber k) S)
  have hcomm (c : k) : q (algebraMap k S c) = algebraMap k A c := by
    change q (algebraMap (DualNumber k) S (algebraMap k (DualNumber k) c)) = algebraMap k A c
    exact hbase (algebraMap k (DualNumber k) c)
  let qk : S →ₐ[k] A := { q with commutes' := hcomm }
  have hqk : Function.Surjective qk := hq
  have hkerq : RingHom.ker qk = J := hker
  have : Algebra.FormallySmooth k ((DualNumber k) ⧸ I) :=
    Algebra.FormallySmooth.of_equiv (dualScalarQuotientEquiv k).symm
  have : Algebra.FormallySmooth k (S ⧸ J) := MappedQuotient.formallySmooth_mapped_quotient (k := k) (S := S) I
  let e : (S ⧸ J) ≃ₐ[k] A :=
    (Ideal.quotientEquivAlgOfEq k hkerq.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hqk)
  exact Algebra.FormallySmooth.of_equiv e

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualSpecialFiber

import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Over

/-! # Mapped Quotient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.MappedQuotient

noncomputable section

/-! Quotienting a formally smooth algebra by an ideal extended from its
base preserves formal smoothness over a smooth quotient of that base. -/

open scoped TensorProduct

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]

theorem formallySmooth_mapped_quotient (I : Ideal R)
    [Algebra.FormallySmooth R S] [Algebra.FormallySmooth k (R ⧸ I)] :
    Algebra.FormallySmooth k (S ⧸ I.map (algebraMap R S)) := by
  have : Algebra.FormallySmooth (R ⧸ I) ((R ⧸ I) ⊗[R] S) := inferInstance
  have : Algebra.FormallySmooth (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    Algebra.FormallySmooth.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm
  have : IsScalarTower k (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    IsScalarTower.to₁₃₄ k R (R ⧸ I) (S ⧸ I.map (algebraMap R S))
  exact Algebra.FormallySmooth.comp k (R ⧸ I) (S ⧸ I.map (algebraMap R S))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.MappedQuotient

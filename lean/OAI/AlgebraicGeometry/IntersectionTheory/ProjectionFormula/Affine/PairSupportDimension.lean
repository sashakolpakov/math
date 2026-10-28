import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ProductDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpecScalarSections
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportAffineInclusion

/-! # Pair Support Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PairSupportDimension

noncomputable section

/-! The tensor-product dimension bound applies to actual reduced
closed supports in the affine product scheme, with its canonical scalar map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct

theorem bound (K A B : Type) [Field K] [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra K A] [Algebra K B]
    [Algebra.FiniteType K A] [Algebra.FiniteType K B]
    (C : IrreducibleCloseds (Spec (.of (A ⊗[K] B)))) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (Spec.map (CommRingCat.ofHom (algebraMap K (A ⊗[K] B)))) ≤
      (Algebra.trdeg K A).toNat + (Algebra.trdeg K B).toNat := by
  let R := A ⊗[K] B
  let X := Spec (.of R)
  let f := Spec.map (CommRingCat.ofHom (algebraMap K R))
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let : Nonempty (Foundations.Scheme.SupportAffineQuotient.supportAffineOpen C U) :=
    (Foundations.Scheme.SupportAffineInclusion.supportAffineOpen_nonempty_iff C U).mpr (by
      obtain ⟨x, hx⟩ := C.isIrreducible.nonempty
      exact ⟨x, hx, trivial⟩)
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.SupportAffineQuotient.supportAffineQuotientScalarAlgebra C f U
  let := Foundations.Scheme.SupportAffineQuotient.supportAffineIdeal_isPrime C U
  let e := SpecScalarSections.equivalence K R
  let ψ : R →ₐ[K] Foundations.Scheme.SupportAffineQuotient.supportAffineQuotient C U :=
    (Ideal.Quotient.mkₐ K ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal C).ideal U)).comp e.toAlgHom
  have hψ : Function.Surjective ψ :=
    (Ideal.Quotient.mk_surjective).comp e.surjective
  let Q := RingHom.ker ψ.toRingHom
  let : Q.IsPrime := RingHom.ker_isPrime ψ.toRingHom
  let eqv : (R ⧸ Q) ≃ₐ[K] Foundations.Scheme.SupportAffineQuotient.supportAffineQuotient C U :=
    Ideal.quotientKerAlgEquivOfSurjective hψ
  rw [Foundations.Scheme.SupportDimension.supportTranscendenceDimension_eq_affineQuotient C f U,
    ← eqv.trdeg_eq]
  exact Tensor.ProductDimension.quotient_toNat K A B Q

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PairSupportDimension

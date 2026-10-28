import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSectionFiniteType
import OAI.AlgebraicGeometry.Foundations.Scheme.StrictTranscendenceDrop
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportAffineInclusion

/-! # Support Dimension Drop -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimensionDrop

noncomputable section

/-!
# Strict dimension drop for irreducible closed supports

The dimension of a support is computed in its actual function field. On an
ambient affine open this is the transcendence degree of the quotient by its
vanishing ideal. Strict inclusion of these prime ideals therefore gives strict
dimension drop, without substituting order-theoretic codimension for dimension.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- Strict inclusion of the actual prime ideals on a common nonempty affine
chart gives strict inequality of the dimensions of the two supports. -/
theorem supportTranscendenceDimension_lt_of_affineIdeal_lt
    (Z W : IrreducibleCloseds X) (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : X.affineOpens) [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)]
    [Nonempty (SupportAffineQuotient.supportAffineOpen W U)]
    (h : (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W).ideal U < (CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal U) :
    SupportDimension.supportTranscendenceDimension Z f < SupportDimension.supportTranscendenceDimension W f := by
  let := SpecScalarTransport.specSectionScalarAlgebra f U
  let := AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U U.2
  let := SupportAffineQuotient.supportAffineIdeal_isPrime Z U
  let := SupportAffineQuotient.supportAffineIdeal_isPrime W U
  rw [SupportDimension.supportTranscendenceDimension_eq_affineQuotient Z f U,
    SupportDimension.supportTranscendenceDimension_eq_affineQuotient W f U]
  exact StrictTranscendenceDrop.trdeg_toNat_quotient_lt_of_prime_lt (k := K) h

/-- A proper irreducible closed subset of an irreducible closed support has
strictly smaller dimension over the base field. -/
theorem supportTranscendenceDimension_lt_of_lt
    (Z W : IrreducibleCloseds X) (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (hZW : Z < W) :
    SupportDimension.supportTranscendenceDimension Z f < SupportDimension.supportTranscendenceDimension W f := by
  obtain ⟨U, hZU, hWU⟩ := SupportAffineInclusion.exists_common_supportAffineOpen Z W hZW.le
  let := hZU
  let := hWU
  exact supportTranscendenceDimension_lt_of_affineIdeal_lt Z W f U
    (SupportAffineInclusion.supportAffineIdeal_lt Z W hZW U)

/-- Dimension is strictly increasing on irreducible closed supports ordered
by inclusion. -/
theorem supportTranscendenceDimension_strictMono
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    StrictMono (fun Z : IrreducibleCloseds X => SupportDimension.supportTranscendenceDimension Z f) := by
  intro Z W hZW
  exact supportTranscendenceDimension_lt_of_lt Z W f hZW

end

end OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimensionDrop

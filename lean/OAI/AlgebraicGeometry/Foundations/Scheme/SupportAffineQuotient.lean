import OAI.AlgebraicGeometry.CycleClass.Geometric.SupportFiniteType
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedImmersionDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Support Affine Quotient -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.SupportAffineQuotient

noncomputable section

/-!
# Affine coordinate rings of actual reduced irreducible supports

An ambient affine open meets a reduced irreducible support in the spectrum of
the quotient by its vanishing ideal. The actual support function field is the
fraction field of this quotient. All maps below come from the closed immersion
and from the structure sheaf, rather than from extra algebraic data.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}}

/-- The open part of a support lying over an ambient affine open. -/
abbrev supportAffineOpen (Z : IrreducibleCloseds X) (U : X.affineOpens) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).Opens :=
  CycleClass.Geometric.GenericPoint.reducedSupportι Z ⁻¹ᵁ U

/-- The actual quotient coordinate ring of the support on an ambient affine open. -/
abbrev supportAffineQuotient (Z : IrreducibleCloseds X) (U : X.affineOpens) :=
  Γ(X, U) ⧸ (CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal U

/-- A closed immersion has affine inverse image of an affine open. -/
theorem supportAffineOpen_isAffine (Z : IrreducibleCloseds X) (U : X.affineOpens) :
    IsAffineOpen (supportAffineOpen Z U) :=
  U.2.preimage (CycleClass.Geometric.GenericPoint.reducedSupportι Z)

/-- The sheaf-theoretic sections are exactly the quotient by the support ideal. -/
def supportAffineSectionsEquiv (Z : IrreducibleCloseds X) (U : X.affineOpens) :
    Γ(CycleClass.Geometric.GenericPoint.reducedSupportScheme Z, supportAffineOpen Z U) ≃+* supportAffineQuotient Z U :=
  ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).subschemeObjIso U).commRingCatIsoToRingEquiv

/-- Pullback of an ambient regular function is its quotient class. -/
theorem supportAffineSectionsEquiv_app (Z : IrreducibleCloseds X) (U : X.affineOpens)
    (a : Γ(X, U)) :
    supportAffineSectionsEquiv Z U ((CycleClass.Geometric.GenericPoint.reducedSupportι Z).app U a) =
      Ideal.Quotient.mk ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal U) a := by
  change ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).subschemeObjIso U).hom
    ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).subschemeι.app U a) = _
  rw [(CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).subschemeι_app U]
  simp

/-- A nonempty open of the integral support has an integral coordinate ring. -/
instance supportAffineQuotient_isDomain (Z : IrreducibleCloseds X) (U : X.affineOpens)
    [Nonempty (supportAffineOpen Z U)] : IsDomain (supportAffineQuotient Z U) :=
  (supportAffineSectionsEquiv Z U).symm.injective.isDomain
    (supportAffineSectionsEquiv Z U).symm

/-- In particular the affine vanishing ideal is prime whenever the open meets
the support. -/
theorem supportAffineIdeal_isPrime (Z : IrreducibleCloseds X) (U : X.affineOpens)
    [Nonempty (supportAffineOpen Z U)] : ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal U).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

/-- The quotient maps to the actual function field by its section isomorphism
and the germ at the generic point. -/
abbrev supportAffineQuotientFunctionFieldAlgebra
    (Z : IrreducibleCloseds X) (U : X.affineOpens) [Nonempty (supportAffineOpen Z U)] :
    Algebra (supportAffineQuotient Z U) (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField :=
  ((algebraMap Γ(CycleClass.Geometric.GenericPoint.reducedSupportScheme Z, supportAffineOpen Z U)
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField).comp
      (supportAffineSectionsEquiv Z U).symm.toRingHom).toAlgebra

/-- The actual function field of the support is the fraction field of its
affine quotient coordinate ring. -/
theorem supportAffineQuotient_isFractionRing
    (Z : IrreducibleCloseds X) (U : X.affineOpens) [Nonempty (supportAffineOpen Z U)] :
    letI := supportAffineQuotientFunctionFieldAlgebra Z U
    IsFractionRing (supportAffineQuotient Z U) (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField := by
  let := supportAffineQuotientFunctionFieldAlgebra Z U
  let := functionField_isFractionRing_of_isAffineOpen (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)
    (supportAffineOpen Z U) (supportAffineOpen_isAffine Z U)
  exact IsFractionRing.of_ringEquiv_left (supportAffineSectionsEquiv Z U).symm
    (fun _ => rfl)

variable {K : Type u} [CommRing K]

/-- The base algebra on the quotient is induced by the ambient structure map. -/
abbrev supportAffineQuotientScalarAlgebra (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) (U : X.affineOpens) : Algebra K (supportAffineQuotient Z U) :=
  letI := SpecScalarTransport.specSectionScalarAlgebra f U
  inferInstance

/-- The affine quotient identification respects the actual base scalar map. -/
def supportAffineSectionsAlgEquiv (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) (U : X.affineOpens) :
    letI := SpecScalarTransport.specSectionScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) (supportAffineOpen Z U)
    letI := supportAffineQuotientScalarAlgebra Z f U
    Γ(CycleClass.Geometric.GenericPoint.reducedSupportScheme Z, supportAffineOpen Z U) ≃ₐ[K] supportAffineQuotient Z U := by
  letI := SpecScalarTransport.specSectionScalarAlgebra f U
  letI := SpecScalarTransport.specSectionScalarAlgebra (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z f) (supportAffineOpen Z U)
  letI := supportAffineQuotientScalarAlgebra Z f U
  refine { supportAffineSectionsEquiv Z U with commutes' := ?_ }
  intro r
  calc
    supportAffineSectionsEquiv Z U
        (algebraMap K Γ(CycleClass.Geometric.GenericPoint.reducedSupportScheme Z, supportAffineOpen Z U) r) =
      supportAffineSectionsEquiv Z U ((CycleClass.Geometric.GenericPoint.reducedSupportι Z).app U
        (algebraMap K Γ(X, U) r)) := by
          exact congrArg (supportAffineSectionsEquiv Z U)
            ((ClosedImmersionDimension.sectionPullbackAlgHom (CycleClass.Geometric.GenericPoint.reducedSupportι Z) f U).commutes r).symm
    _ = Ideal.Quotient.mk ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal U)
        (algebraMap K Γ(X, U) r) := supportAffineSectionsEquiv_app Z U _
    _ = algebraMap K (supportAffineQuotient Z U) r := rfl

end

end OAI.AlgebraicGeometry.Foundations.Scheme.SupportAffineQuotient

import OAI.AlgebraicGeometry.Foundations.Scheme.CycleSupports
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Generic Point -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.GenericPoint

noncomputable section

/-!
# Integral closed subschemes representing cycle supports

An irreducible closed subset of a scheme carries its reduced induced scheme
structure. This file constructs that actual scheme from mathlib's vanishing
ideal sheaf, proves it is integral, and identifies its generic point with the
point indexing the algebraic cycle support.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}}

/-- The radical ideal sheaf defining the reduced structure on a closed support. -/
def reducedSupportIdeal (Z : IrreducibleCloseds X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨Z, Z.isClosed⟩

/-- The actual reduced induced closed subscheme on an irreducible support. -/
def reducedSupportScheme (Z : IrreducibleCloseds X) : Scheme.{u} :=
  (reducedSupportIdeal Z).subscheme

/-- The closed immersion of the reduced induced support into its ambient scheme. -/
def reducedSupportι (Z : IrreducibleCloseds X) : reducedSupportScheme Z ⟶ X :=
  (reducedSupportIdeal Z).subschemeι

instance reducedSupportι_isClosedImmersion (Z : IrreducibleCloseds X) :
    IsClosedImmersion (reducedSupportι Z) := by
  exact inferInstanceAs (IsClosedImmersion (reducedSupportIdeal Z).subschemeι)

@[simp]
theorem range_reducedSupportι (Z : IrreducibleCloseds X) :
    Set.range (reducedSupportι Z) = (Z : Set X) := by
  change Set.range (reducedSupportIdeal Z).subschemeι = (Z : Set X)
  rw [Scheme.IdealSheafData.range_subschemeι]
  simp [reducedSupportIdeal]

instance reducedSupportScheme_isReduced (Z : IrreducibleCloseds X) :
    AlgebraicGeometry.IsReduced (reducedSupportScheme Z) := by
  let I := reducedSupportIdeal Z
  change AlgebraicGeometry.IsReduced I.subscheme
  apply (AlgebraicGeometry.IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover).2
  intro U
  change X.affineOpens at U
  change AlgebraicGeometry.IsReduced (Spec (.of (Γ(X, U) ⧸ I.ideal U)))
  apply (AlgebraicGeometry.affine_isReduced_iff _).2
  apply (Ideal.isRadical_iff_quotient_reduced _).1
  change (PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set X))).IsRadical
  exact PrimeSpectrum.isRadical_vanishingIdeal _

instance reducedSupportScheme_irreducible (Z : IrreducibleCloseds X) :
    IrreducibleSpace (reducedSupportScheme Z) := by
  exact Subtype.irreducibleSpace Z.isIrreducible

instance reducedSupportScheme_isIntegral (Z : IrreducibleCloseds X) :
    IsIntegral (reducedSupportScheme Z) :=
  AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced _

/-- The generic point of the reduced support has the stated irreducible closure
in the ambient scheme. -/
theorem reducedSupport_genericPoint (Z : IrreducibleCloseds X) :
    IsGenericPoint ((reducedSupportι Z) (genericPoint (reducedSupportScheme Z)))
      (Z : Set X) := by
  have h := (genericPoint_spec (reducedSupportScheme Z)).image
    (reducedSupportι Z).continuous
  simpa only [Set.image_univ, range_reducedSupportι, Z.isClosed.closure_eq] using h

/-- The scheme-theoretic generic point agrees with the existing sober-space
correspondence used to index cycles. -/
theorem reducedSupport_genericPoint_eq (Z : IrreducibleCloseds X) :
    (reducedSupportι Z) (genericPoint (reducedSupportScheme Z)) =
      irreducibleSetEquivPoints Z := by
  exact (reducedSupport_genericPoint Z).eq
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed)

/-- For a codimension-indexed support, its actual integral closed subscheme has
exactly the prescribed codimension at its generic point. -/
theorem reducedSupport_genericPoint_codimension (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport X p) :
    Order.coheight ((reducedSupportι Z.1)
      (genericPoint (reducedSupportScheme Z.1))) = p := by
  rw [reducedSupport_genericPoint_eq]
  exact (Foundations.Scheme.CycleSupports.irreducibleCycleSupportEquivCyclePoint X p Z).2

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.GenericPoint

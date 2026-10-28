import OAI.AlgebraicGeometry.DivisorClass.Chern.HeightOneDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportAffineInclusion
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSectionFiniteType

/-! # Support Codimension -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension

noncomputable section

/-!
# ChernClass: codimension-one scheme points give dimension-graded divisor supports

The affine ideal of the closure of a point is its actual prime ideal on an
affine chart. Its height is the point's specialization coheight. The proved
finite-type height-one formula identifies the support dimension exactly.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Construction

variable {X : Scheme}

/-- The reduced affine ideal of a point's closure is precisely the point's affine prime. -/
theorem pointClosure_affineIdeal (x : X) (U : X.affineOpens) (hx : x ∈ U.1) :
    (CycleClass.Geometric.GenericPoint.reducedSupportIdeal (irreducibleSetEquivPoints.symm x)).ideal U =
      (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' closure {x}) = _
  rw [U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    U.2.fromSpec.continuous]
  have hp : U.2.fromSpec ⁻¹' {x} = {U.2.primeIdealOf ⟨x, hx⟩} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hy
      apply U.2.fromSpec.isOpenEmbedding.injective
      rw [U.2.fromSpec_primeIdealOf, hy]
    · intro hy
      rw [hy, U.2.fromSpec_primeIdealOf]
  rw [hp, PrimeSpectrum.vanishingIdeal_closure, PrimeSpectrum.vanishingIdeal_singleton]

/-- The affine prime height is the scheme point's actual specialization coheight. -/
theorem pointClosure_affineIdeal_height (x : X) (U : X.affineOpens) (hx : x ∈ U.1) :
    ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal (irreducibleSetEquivPoints.symm x)).ideal U).height = Order.coheight x := by
  rw [pointClosure_affineIdeal x U hx]
  calc
    (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.height =
        Order.coheight (show Spec Γ(X, U) from U.2.primeIdealOf ⟨x, hx⟩) :=
      idealHeight_eq_coheight Γ(X, U) _
    _ = Order.coheight x := by
      rw [← coheight_eq_of_isOpenImmersion U.2.fromSpec, U.2.fromSpec_primeIdealOf]

/-- A codimension-one point has support dimension exactly one less than the ambient integral scheme. -/
theorem pointClosure_dimension_add_one [IsIntegral X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (x : X) (hx : Order.coheight x = 1) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + 1 =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let V : X.affineOpens := ⟨U, hU⟩
  let Z : IrreducibleCloseds X := irreducibleSetEquivPoints.symm x
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : Nonempty (Foundations.Scheme.SupportAffineQuotient.supportAffineOpen Z V) := (Foundations.Scheme.SupportAffineInclusion.supportAffineOpen_nonempty_iff Z V).mpr
    ⟨x, subset_closure (Set.mem_singleton x), hxU⟩
  let : Algebra ℂ Γ(X, U) := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let : Algebra.FiniteType ℂ Γ(X, U) := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U hU
  let : ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal V).IsPrime := Foundations.Scheme.SupportAffineQuotient.supportAffineIdeal_isPrime Z V
  have hp : ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal V).height = 1 :=
    (pointClosure_affineIdeal_height x V hxU).trans hx
  rw [Foundations.Scheme.SupportDimension.supportTranscendenceDimension_eq_affineQuotient Z f V,
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections f U hU]
  exact HeightOneDimension.Construction.finiteType_height_one_trdeg ℂ Γ(X, U) ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal V) hp

end Construction

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension

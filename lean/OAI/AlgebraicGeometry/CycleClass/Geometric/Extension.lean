import OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainTriple
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainFunctoriality

/-! # Extension -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric

noncomputable section

section

/-!
# The actual relative pair of a cycle support's regular locus

Inside the complement of the singular boundary, the complement of the regular
locus is precisely the inverse image of the complement of the original
support. The isomorphisms below use identity maps of these actual pairs, rather
than transports between externally supplied cohomology groups.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
variable {R : Type} [Ring R]

/-- The complement of the support is contained in the complement of its
singular boundary, as needed by the genuine relative triple. -/
theorem DimensionCycles.DimensionCycleSupport.analyticSupportComplement_subset_regularAmbient (Z : DimensionCycles.DimensionCycleSupport V p) :
    (Set.range Z.analyticInclusion)ᶜ ⊆ Z.analyticSingularBoundaryᶜ :=
  Set.compl_subset_compl.mpr Z.analyticSingularBoundary_subset_range

/-- The complement of the regular-locus range has the expected pointwise
description in the actual boundary complement. -/
theorem DimensionCycles.DimensionCycleSupport.mem_regularThomComplement_iff (Z : DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAmbientSpace) :
    x ∉ Set.range Z.regularComplementInclusion ↔
      x.val ∉ Set.range Z.analyticInclusion := by
  rw [Z.range_regularComplementInclusion]
  rfl

/-- The regular-locus pair is the literal inner pair of the ambient triple. -/
theorem DimensionCycles.DimensionCycleSupport.regularThomComplement_eq_tripleSubspace (Z : DimensionCycles.DimensionCycleSupport V p) :
    (Set.range Z.regularComplementInclusion)ᶜ =
      RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of V.analyticSpace)
        Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ := by
  ext x
  exact Z.mem_regularThomComplement_iff x

/-- The same removed subset is the literal preimage of the algebraic support
complement under the actual underlying-point map. -/
theorem DimensionCycles.DimensionCycleSupport.regularThomComplement_eq_algebraicPreimage (Z : DimensionCycles.DimensionCycleSupport V p) :
    (Set.range Z.regularComplementInclusion)ᶜ =
      (fun x : Z.regularAmbientSpace => V.analyticUnderlying x.val) ⁻¹'
        (Z.1 : Set V.carrier)ᶜ := by
  rw [Z.range_regularComplementInclusion, Z.range_analyticInclusion]
  rfl

/-- Identity maps of the identified pairs give a canonical isomorphism of
their actual relative cochain kernels. The forward map has the literal
triple pair as its target. -/
def DimensionCycles.DimensionCycleSupport.regularThomCochainsIso (M : ModuleCat.{0} R) (Z : DimensionCycles.DimensionCycleSupport V p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M (TopCat.of Z.regularAmbientSpace)
        (Set.range Z.regularComplementInclusion)ᶜ ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M (TopCat.of (Z.analyticSingularBoundaryᶜ : Set V.analyticSpace))
        (RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of V.analyticSpace)
          Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ) where
  hom := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (𝟙 (TopCat.of Z.regularAmbientSpace))
    (fun x hx => (Z.mem_regularThomComplement_iff x).mpr hx)
  inv := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (𝟙 (TopCat.of Z.regularAmbientSpace))
    (fun x hx => (Z.mem_regularThomComplement_iff x).mp hx)
  hom_inv_id := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp_eq_id M _ _
    (fun x hx => (Z.mem_regularThomComplement_iff x).mp hx)
    (fun x hx => (Z.mem_regularThomComplement_iff x).mpr hx) (Category.id_comp _)
  inv_hom_id := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp_eq_id M _ _
    (fun x hx => (Z.mem_regularThomComplement_iff x).mpr hx)
    (fun x hx => (Z.mem_regularThomComplement_iff x).mp hx) (Category.id_comp _)

@[simp]
theorem DimensionCycles.DimensionCycleSupport.regularThomCochainsIso_hom (M : ModuleCat.{0} R) (Z : DimensionCycles.DimensionCycleSupport V p) :
    (Z.regularThomCochainsIso M).hom =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (𝟙 (TopCat.of Z.regularAmbientSpace))
        (fun x hx => (Z.mem_regularThomComplement_iff x).mpr hx) := rfl

@[simp]
theorem DimensionCycles.DimensionCycleSupport.regularThomCochainsIso_inv (M : ModuleCat.{0} R) (Z : DimensionCycles.DimensionCycleSupport V p) :
    (Z.regularThomCochainsIso M).inv =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (𝟙 (TopCat.of Z.regularAmbientSpace))
        (fun x hx => (Z.mem_regularThomComplement_iff x).mp hx) := rfl

/-- The identification preserves the actual inclusion into absolute cochains. -/
@[reassoc (attr := simp)]
theorem DimensionCycles.DimensionCycleSupport.regularThomCochainsIso_hom_inclusion (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) :
    (Z.regularThomCochainsIso M).hom ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M (TopCat.of (Z.analyticSingularBoundaryᶜ : Set V.analyticSpace))
          (RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of V.analyticSpace)
            Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M (TopCat.of Z.regularAmbientSpace)
        (Set.range Z.regularComplementInclusion)ᶜ := by
  simpa only [AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_id, Category.comp_id] using!
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality M (𝟙 (TopCat.of Z.regularAmbientSpace))
      (A := RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of V.analyticSpace)
        Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ)
      (B := (Set.range Z.regularComplementInclusion)ᶜ)
      (fun x hx => (Z.mem_regularThomComplement_iff x).mpr hx))

/-- The inverse identification also preserves the actual absolute cochain. -/
@[reassoc (attr := simp)]
theorem DimensionCycles.DimensionCycleSupport.regularThomCochainsIso_inv_inclusion (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) :
    (Z.regularThomCochainsIso M).inv ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M (TopCat.of Z.regularAmbientSpace)
          (Set.range Z.regularComplementInclusion)ᶜ =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M (TopCat.of (Z.analyticSingularBoundaryᶜ : Set V.analyticSpace))
        (RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of V.analyticSpace)
          Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ) := by
  simpa only [AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_id, Category.comp_id] using!
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality M (𝟙 (TopCat.of Z.regularAmbientSpace))
      (A := (Set.range Z.regularComplementInclusion)ᶜ)
      (B := RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of V.analyticSpace)
        Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ)
      (fun x hx => (Z.mem_regularThomComplement_iff x).mp hx))

/-- The same canonical pair identification in every cohomological degree. -/
def DimensionCycles.DimensionCycleSupport.regularThomCohomologyIso (M : ModuleCat.{0} R) (Z : DimensionCycles.DimensionCycleSupport V p)
    (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of Z.regularAmbientSpace)
        (Set.range Z.regularComplementInclusion)ᶜ n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of (Z.analyticSingularBoundaryᶜ : Set V.analyticSpace))
        (RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of V.analyticSpace)
          Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n).mapIso
    (Z.regularThomCochainsIso M)

@[simp]
theorem DimensionCycles.DimensionCycleSupport.regularThomCohomologyIso_hom (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) (n : ℕ) :
    (Z.regularThomCohomologyIso M n).hom =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (𝟙 (TopCat.of Z.regularAmbientSpace))
        (fun x hx => (Z.mem_regularThomComplement_iff x).mpr hx) n := rfl

@[simp]
theorem DimensionCycles.DimensionCycleSupport.regularThomCohomologyIso_inv (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) (n : ℕ) :
    (Z.regularThomCohomologyIso M n).inv =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (𝟙 (TopCat.of Z.regularAmbientSpace))
        (fun x hx => (Z.mem_regularThomComplement_iff x).mp hx) n := rfl

/-- Forgetting support before or after the pair identification is the same map. -/
@[reassoc (attr := simp)]
theorem DimensionCycles.DimensionCycleSupport.regularThomCohomologyIso_hom_inclusion (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) (n : ℕ) :
    (Z.regularThomCohomologyIso M n).hom ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M (TopCat.of (Z.analyticSingularBoundaryᶜ : Set V.analyticSpace))
          (RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of V.analyticSpace)
            Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ) n =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M (TopCat.of Z.regularAmbientSpace)
        (Set.range Z.regularComplementInclusion)ᶜ n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n = _
  rw [← HomologicalComplex.homologyMap_comp, DimensionCycles.DimensionCycleSupport.regularThomCochainsIso_hom_inclusion]

@[reassoc (attr := simp)]
theorem DimensionCycles.DimensionCycleSupport.regularThomCohomologyIso_inv_inclusion (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) (n : ℕ) :
    (Z.regularThomCohomologyIso M n).inv ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M (TopCat.of Z.regularAmbientSpace)
          (Set.range Z.regularComplementInclusion)ᶜ n =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M (TopCat.of (Z.analyticSingularBoundaryᶜ : Set V.analyticSpace))
        (RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of V.analyticSpace)
          Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ) n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n = _
  rw [← HomologicalComplex.homologyMap_comp, DimensionCycles.DimensionCycleSupport.regularThomCochainsIso_inv_inclusion]

/-- Pointwise, the identified relative class has exactly the same absolute
class on the boundary complement. -/
theorem DimensionCycles.DimensionCycleSupport.regularThomCohomologyIso_forget_apply (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of Z.regularAmbientSpace)
      (Set.range Z.regularComplementInclusion)ᶜ n) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M (TopCat.of (Z.analyticSingularBoundaryᶜ : Set V.analyticSpace))
        (RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of V.analyticSpace)
          Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ) n
        ((Z.regularThomCohomologyIso M n).hom c) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M (TopCat.of Z.regularAmbientSpace)
        (Set.range Z.regularComplementInclusion)ᶜ n c :=
  ConcreteCategory.congr_hom (Z.regularThomCohomologyIso_hom_inclusion M n) c

/-- The actual restriction from the ambient support pair to the regular-locus
pair is induced by the inclusion of the boundary complement. -/
def DimensionCycles.DimensionCycleSupport.regularThomCochainRestriction (M : ModuleCat.{0} R) (Z : DimensionCycles.DimensionCycleSupport V p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M (TopCat.of V.analyticSpace)
        (Set.range Z.analyticInclusion)ᶜ ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M (TopCat.of Z.regularAmbientSpace)
        (Set.range Z.regularComplementInclusion)ᶜ :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M
    (LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) Z.analyticSingularBoundaryᶜ)
    (fun x hx => (Z.mem_regularThomComplement_iff x).mp hx)

/-- Restriction to the regular-locus pair has exactly the ordinary ambient
restriction as its underlying map of cochains. -/
@[reassoc (attr := simp)]
theorem DimensionCycles.DimensionCycleSupport.regularThomCochainRestriction_inclusion (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) :
    Z.regularThomCochainRestriction M ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M (TopCat.of Z.regularAmbientSpace)
          (Set.range Z.regularComplementInclusion)ᶜ =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M (TopCat.of V.analyticSpace)
          (Set.range Z.analyticInclusion)ᶜ ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M (TopCat.of V.analyticSpace)
          Z.analyticSingularBoundaryᶜ :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality M
    (LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) Z.analyticSingularBoundaryᶜ)
    (fun x hx => (Z.mem_regularThomComplement_iff x).mp hx)

/-- Identifying the target pair turns actual restriction into the literal
restriction map in the existing relative triple sequence. -/
@[reassoc]
theorem DimensionCycles.DimensionCycleSupport.regularThomCochainRestriction_triple (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) :
    Z.regularThomCochainRestriction M ≫ (Z.regularThomCochainsIso M).hom =
      RelativeCochainTriple.Cohomology.relativeCochainTripleRestriction M (TopCat.of V.analyticSpace)
        Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ := by
  apply (cancel_mono (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M
    (TopCat.of (Z.analyticSingularBoundaryᶜ : Set V.analyticSpace))
    (RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ))).1
  rw [Category.assoc, DimensionCycles.DimensionCycleSupport.regularThomCochainsIso_hom_inclusion,
    DimensionCycles.DimensionCycleSupport.regularThomCochainRestriction_inclusion, RelativeCochainTriple.Cohomology.relativeCochainTripleRestriction_inclusion]

/-- The inverse identification recovers the genuine regular-locus restriction. -/
@[reassoc]
theorem DimensionCycles.DimensionCycleSupport.relativeCochainTripleRestriction_regularThom (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) :
    RelativeCochainTriple.Cohomology.relativeCochainTripleRestriction M (TopCat.of V.analyticSpace)
        Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ ≫
        (Z.regularThomCochainsIso M).inv =
      Z.regularThomCochainRestriction M := by
  rw [← DimensionCycles.DimensionCycleSupport.regularThomCochainRestriction_triple M Z, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Actual restriction to the regular-locus pair on relative cohomology. -/
abbrev DimensionCycles.DimensionCycleSupport.regularThomCohomologyRestriction (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
        (Set.range Z.analyticInclusion)ᶜ n ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of Z.regularAmbientSpace)
        (Set.range Z.regularComplementInclusion)ᶜ n :=
  HomologicalComplex.homologyMap (Z.regularThomCochainRestriction M) n

@[simp]
theorem DimensionCycles.DimensionCycleSupport.regularThomCohomologyRestriction_eq_pairPullback (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) (n : ℕ) :
    Z.regularThomCohomologyRestriction M n =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M
        (LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) Z.analyticSingularBoundaryᶜ)
        (fun x hx => (Z.mem_regularThomComplement_iff x).mp hx) n := rfl

/-- The cohomological restriction is the one used by the triple extension. -/
@[reassoc]
theorem DimensionCycles.DimensionCycleSupport.regularThomCohomologyRestriction_triple (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) (n : ℕ) :
    Z.regularThomCohomologyRestriction M n ≫ (Z.regularThomCohomologyIso M n).hom =
      RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction M (TopCat.of V.analyticSpace)
        Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n = _
  rw [← HomologicalComplex.homologyMap_comp, DimensionCycles.DimensionCycleSupport.regularThomCochainRestriction_triple]

@[reassoc]
theorem DimensionCycles.DimensionCycleSupport.relativeCohomologyTripleRestriction_regularThom (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) (n : ℕ) :
    RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction M (TopCat.of V.analyticSpace)
        Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ n ≫
        (Z.regularThomCohomologyIso M n).inv =
      Z.regularThomCohomologyRestriction M n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n = _
  rw [← HomologicalComplex.homologyMap_comp, DimensionCycles.DimensionCycleSupport.relativeCochainTripleRestriction_regularThom]

/-- Forgetting supports after regular-locus restriction is ordinary restriction
of the ambient absolute cohomology class. -/
@[reassoc (attr := simp)]
theorem DimensionCycles.DimensionCycleSupport.regularThomCohomologyRestriction_inclusion (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) (n : ℕ) :
    Z.regularThomCohomologyRestriction M n ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M (TopCat.of Z.regularAmbientSpace)
          (Set.range Z.regularComplementInclusion)ᶜ n =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M (TopCat.of V.analyticSpace)
          (Set.range Z.analyticInclusion)ᶜ n ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCohomologyRestriction M (TopCat.of V.analyticSpace)
          Z.analyticSingularBoundaryᶜ n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    DimensionCycles.DimensionCycleSupport.regularThomCochainRestriction_inclusion]

end

/-!
# Extending the actual regular-locus relative class

This is the geometric specialization of the proved relative-cohomology
triple isomorphism. Its two vanishing hypotheses are explicit; the algebraic
singular-boundary purity theorem will discharge them when the cycle class
is constructed. No class on the regular locus is postulated.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
variable {R : Type} [Ring R]

/-- Restrict a supported ambient class to the actual regular-locus Thom pair. -/
def DimensionCycles.DimensionCycleSupport.regularSupportRestriction (M : ModuleCat.{0} R) (Z : DimensionCycles.DimensionCycleSupport V p)
    (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
        (Set.range Z.analyticInclusion)ᶜ n ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of Z.regularAmbientSpace)
        (Set.range Z.regularComplementInclusion)ᶜ n :=
  RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ n ≫
    (Z.regularThomCohomologyIso M n).inv

/-- The genuine extension isomorphism, assuming the two precise obstruction
groups vanish. Its inverse is restriction to the actual regular-locus pair. -/
def DimensionCycles.DimensionCycleSupport.regularToSupportCohomologyIso (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) (n : ℕ)
    (h₀ : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ n))
    (h₁ : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ (n + 1))) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of Z.regularAmbientSpace)
        (Set.range Z.regularComplementInclusion)ᶜ n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
        (Set.range Z.analyticInclusion)ᶜ n :=
  Z.regularThomCohomologyIso M n ≪≫
    (RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestrictionIso M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ
      Z.analyticSupportComplement_subset_regularAmbient n h₀ h₁).symm

@[simp]
theorem DimensionCycles.DimensionCycleSupport.regularToSupportCohomologyIso_inv (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) (n : ℕ)
    (h₀ : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ n))
    (h₁ : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ (n + 1))) :
    (Z.regularToSupportCohomologyIso M n h₀ h₁).inv =
      Z.regularSupportRestriction M n := rfl

@[simp]
theorem DimensionCycles.DimensionCycleSupport.regularToSupportCohomologyIso_hom (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) (n : ℕ)
    (h₀ : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ n))
    (h₁ : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ (n + 1))) :
    (Z.regularToSupportCohomologyIso M n h₀ h₁).hom =
      (Z.regularThomCohomologyIso M n).hom ≫
        RelativeCochainTriple.Cohomology.relativeCohomologyTripleExtension M (TopCat.of V.analyticSpace)
          Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ
          Z.analyticSupportComplement_subset_regularAmbient n h₀ h₁ := rfl

@[reassoc (attr := simp)]
theorem DimensionCycles.DimensionCycleSupport.regularToSupportCohomologyIso_hom_restriction (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) (n : ℕ)
    (h₀ : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ n))
    (h₁ : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ (n + 1))) :
    (Z.regularToSupportCohomologyIso M n h₀ h₁).hom ≫
      Z.regularSupportRestriction M n = 𝟙 _ :=
  (Z.regularToSupportCohomologyIso M n h₀ h₁).hom_inv_id

/-- The extended supported class is uniquely characterized by its genuine
restriction to the regular-locus pair. -/
theorem DimensionCycles.DimensionCycleSupport.regularToSupportCohomologyIso_unique (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) (n : ℕ)
    (h₀ : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ n))
    (h₁ : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ (n + 1)))
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of Z.regularAmbientSpace)
      (Set.range Z.regularComplementInclusion)ᶜ n)
    (z : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      (Set.range Z.analyticInclusion)ᶜ n)
    (hz : Z.regularSupportRestriction M n z = c) :
    z = (Z.regularToSupportCohomologyIso M n h₀ h₁).hom c := by
  let e := Z.regularToSupportCohomologyIso M n h₀ h₁
  have h : e.inv z = c := hz
  calc
    z = e.hom (e.inv z) :=
      (ConcreteCategory.congr_hom e.inv_hom_id z).symm
    _ = e.hom c := congrArg e.hom h

/-- Extend through the singular boundary, then forget support. This is a
morphism of actual cohomology modules, hence is linear in the input class. -/
def DimensionCycles.DimensionCycleSupport.regularToAbsoluteCohomology (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) (n : ℕ)
    (h₀ : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ n))
    (h₁ : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ (n + 1))) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of Z.regularAmbientSpace)
        (Set.range Z.regularComplementInclusion)ᶜ n ⟶
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology M (TopCat.of V.analyticSpace) n :=
  (Z.regularToSupportCohomologyIso M n h₀ h₁).hom ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M (TopCat.of V.analyticSpace)
      (Set.range Z.analyticInclusion)ᶜ n

@[simp]
theorem DimensionCycles.DimensionCycleSupport.regularToAbsoluteCohomology_apply (M : ModuleCat.{0} R)
    (Z : DimensionCycles.DimensionCycleSupport V p) (n : ℕ)
    (h₀ : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ n))
    (h₁ : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
      Z.analyticSingularBoundaryᶜ (n + 1)))
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of Z.regularAmbientSpace)
      (Set.range Z.regularComplementInclusion)ᶜ n) :
    Z.regularToAbsoluteCohomology M n h₀ h₁ c =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M (TopCat.of V.analyticSpace)
        (Set.range Z.analyticInclusion)ᶜ n
        ((Z.regularToSupportCohomologyIso M n h₀ h₁).hom c) := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric

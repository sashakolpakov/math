import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedAbsoluteClass
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum

/-! # Open Supported Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenSupportedCycle.BundleCycles

noncomputable section

section

/-! Genuine finite dimension-graded cycles in a common analytic support, with their canonical supported cycle class. Supports missing the open contribute zero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (S : Set U) (d : ℕ)

abbrev schemeOpenSupportedPoint := {x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d //
  (Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) ⁻¹'
    Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm x.val)) ⊆ S}

abbrev schemeOpenSupportedCycle := schemeOpenSupportedPoint X U S d →₀ ℚ

def schemeOpenSupportedCycle_forget : schemeOpenSupportedCycle X U S d →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (fun x : schemeOpenSupportedPoint X U S d => x.val)

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeOpenSupportedCycle_forget_apply (c : schemeOpenSupportedCycle X U S d)
    (x : schemeOpenSupportedPoint X U S d) : schemeOpenSupportedCycle_forget X U S d c x.val = c x :=
  Finsupp.mapDomain_apply_of_injective Subtype.val_injective c x

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeOpenSupportedPoint_mapsTo (x : schemeOpenSupportedPoint X U S d) :
    Set.MapsTo (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
      Sᶜ (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm x.val.val)))ᶜ :=
  fun _ hx hy => hx (x.property hy)

variable (p : ℕ) (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

def schemeOpenRelativeGenerator (x : schemeOpenSupportedPoint X U S d) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) Sᶜ (2 * p) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (schemeOpenSupportedPoint_mapsTo X U S d x) (2 * p)
    (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X (irreducibleSetEquivPoints.symm x.val.val) p
      ((congrArg (fun n => n + p) x.val.property).trans hd))

def schemeOpenRelativeClassMap : schemeOpenSupportedCycle X U S d →ₗ[ℚ]
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) Sᶜ (2 * p) :=
  Finsupp.linearCombination ℚ (schemeOpenRelativeGenerator X U S d p hd)

theorem schemeOpenRelativeClassMap_single (x : schemeOpenSupportedPoint X U S d) (r : ℚ) :
    schemeOpenRelativeClassMap X U S d p hd (Finsupp.single x r) =
      r • schemeOpenRelativeGenerator X U S d p hd x := Finsupp.linearCombination_single ℚ r x

theorem schemeOpenRelativeGenerator_zero_of_disjoint (x : schemeOpenSupportedPoint X U S d)
    (hx : ∀ y : U, y.val ∉ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm x.val.val))) :
    schemeOpenRelativeGenerator X U S d p hd x = 0 := by
  have h := DivisorClass.Chern.SupportedDivisorSum.relativeCohomologyMap_zero_of_range_subset (ModuleCat.of ℚ ℚ)
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) Sᶜ
    (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm x.val.val)))ᶜ
    (schemeOpenSupportedPoint_mapsTo X U S d x) hx (2 * p)
  exact ConcreteCategory.congr_hom h
    (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X (irreducibleSetEquivPoints.symm x.val.val) p
      ((congrArg (fun n => n + p) x.val.property).trans hd))

theorem schemeOpenRelativeClassMap_eq_of_local_coefficients (c e : schemeOpenSupportedCycle X U S d)
    (h : ∀ x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d,
      (∃ y : U, y.val ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm x.val))) →
        schemeOpenSupportedCycle_forget X U S d c x = schemeOpenSupportedCycle_forget X U S d e x) :
    schemeOpenRelativeClassMap X U S d p hd c = schemeOpenRelativeClassMap X U S d p hd e := by
  classical
  apply sub_eq_zero.mp
  rw [← map_sub, schemeOpenRelativeClassMap, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : ∃ y : U, y.val ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm x.val.val))
  · have hc := h x.val hx
    rw [schemeOpenSupportedCycle_forget_apply, schemeOpenSupportedCycle_forget_apply] at hc
    rw [Finsupp.sub_apply, hc, sub_self, zero_smul]
  · have hz := schemeOpenRelativeGenerator_zero_of_disjoint X U S d p hd x (by simpa only [not_exists] using hx)
    rw [hz, smul_zero]

end

section

/-! A finite graded cycle supported on the retained analytic open lifts to the canonical common-support cycle module; its class depends only on coefficients of supports meeting that open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (S : Set U) (d p : ℕ)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

def schemeOpenRestrictCycle (c : (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ)) : schemeOpenSupportedCycle X U S d :=
  Finsupp.subtypeDomain (fun D : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d =>
    (Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm D.val)) ⊆ S) c

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeOpenRestrictCycle_apply (c : (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ)) (D : schemeOpenSupportedPoint X U S d) :
    schemeOpenRestrictCycle X U S d c D = c D.val := rfl

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeOpen_forget_restrictCycle (c : (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ))
    (hc : ∀ D : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d, c D ≠ 0 →
      (Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm D.val)) ⊆ S) :
    schemeOpenSupportedCycle_forget X U S d (schemeOpenRestrictCycle X U S d c) = c := by
  classical
  ext D
  by_cases hD : (Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm D.val)) ⊆ S
  · exact (schemeOpenSupportedCycle_forget_apply X U S d (schemeOpenRestrictCycle X U S d c) ⟨D, hD⟩).trans rfl
  · have hz : c D = 0 := by
      by_contra hn
      exact hD (hc D hn)
    rw [hz]
    exact Finsupp.mapDomain_of_notMem_range (schemeOpenRestrictCycle X U S d c) D (by
      rintro ⟨E, he⟩
      exact hD (he ▸ E.property))

theorem schemeOpen_supportedClass_eq_of_local_coefficients (c e : (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ))
    (hc : ∀ D : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d, c D ≠ 0 →
      (Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm D.val)) ⊆ S)
    (he : ∀ D : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d, e D ≠ 0 →
      (Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm D.val)) ⊆ S)
    (hcoeff : ∀ D : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d, (∃ x : U, x.val ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm D.val))) → c D = e D) :
    schemeOpenRelativeClassMap X U S d p hd (schemeOpenRestrictCycle X U S d c) =
      schemeOpenRelativeClassMap X U S d p hd (schemeOpenRestrictCycle X U S d e) := by
  apply schemeOpenRelativeClassMap_eq_of_local_coefficients X U S d p hd
  intro D hD
  rw [schemeOpen_forget_restrictCycle X U S d c hc, schemeOpen_forget_restrictCycle X U S d e he]
  exact hcoeff D hD

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeOpen_forgetCycle_supported (c : schemeOpenSupportedCycle X U S d) (D : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d)
    (hc : schemeOpenSupportedCycle_forget X U S d c D ≠ 0) :
    (Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm D.val)) ⊆ S := by
  have hr : D ∈ Set.range (fun E : schemeOpenSupportedPoint X U S d => E.val) :=
    Finsupp.mem_range_of_mapDomain_ne_zero hc
  obtain ⟨E, hE⟩ := hr
  exact hE ▸ E.property

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeOpen_supports_of_local_coefficients (c : schemeOpenSupportedCycle X U S d) (e : (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ))
    (hcoeff : ∀ D : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d, (∃ x : U, x.val ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm D.val))) →
      schemeOpenSupportedCycle_forget X U S d c D = e D) :
    ∀ D : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d, e D ≠ 0 →
      (Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm D.val)) ⊆ S := by
  intro D hD x hx
  have hc : schemeOpenSupportedCycle_forget X U S d c D ≠ 0 := by
    rw [hcoeff D ⟨x, hx⟩]
    exact hD
  exact schemeOpen_forgetCycle_supported X U S d c D hc hx

theorem schemeOpenRelativeClassMap_eq_restrict_of_local_coefficients
    (c : schemeOpenSupportedCycle X U S d) (e : (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ))
    (hcoeff : ∀ D : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d, (∃ x : U, x.val ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm D.val))) →
      schemeOpenSupportedCycle_forget X U S d c D = e D) :
    schemeOpenRelativeClassMap X U S d p hd c = schemeOpenRelativeClassMap X U S d p hd (schemeOpenRestrictCycle X U S d e) := by
  apply schemeOpenRelativeClassMap_eq_of_local_coefficients X U S d p hd
  intro D hD
  rw [schemeOpen_forget_restrictCycle X U S d e (schemeOpen_supports_of_local_coefficients X U S d c e hcoeff)]
  exact hcoeff D hD

end

section

/-! Finite dimension-graded cycles in an actual global closed support carry the linear combination of their canonical supported classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (F : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (d : ℕ)

abbrev schemeClosedSupportedPoint := {x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d //
  Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm x.val)) ⊆ F}

abbrev schemeClosedSupportedCycle := schemeClosedSupportedPoint X F d →₀ ℚ

def schemeClosedSupportedCycle_forget : schemeClosedSupportedCycle X F d →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (fun x : schemeClosedSupportedPoint X F d => x.val)

def schemeClosedRestrictCycle (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) : schemeClosedSupportedCycle X F d :=
  Finsupp.subtypeDomain (fun x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d =>
    Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm x.val)) ⊆ F) c

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeClosedSupportedCycle_forget_apply (c : schemeClosedSupportedCycle X F d)
    (x : schemeClosedSupportedPoint X F d) : schemeClosedSupportedCycle_forget X F d c x.val = c x :=
  Finsupp.mapDomain_apply_of_injective Subtype.val_injective c x

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeClosedSupportedPoint_mapsTo (x : schemeClosedSupportedPoint X F d) :
    Set.MapsTo (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) Fᶜ
      (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm x.val.val)))ᶜ :=
  fun _ hx hy => hx (x.property hy)

variable (p : ℕ) (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

def schemeClosedRelativeGenerator (x : schemeClosedSupportedPoint X F d) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) Fᶜ (2 * p) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (schemeClosedSupportedPoint_mapsTo X F d x) (2 * p)
    (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X (irreducibleSetEquivPoints.symm x.val.val) p
      ((congrArg (fun n => n + p) x.val.property).trans hd))

def schemeClosedRelativeClassMap : schemeClosedSupportedCycle X F d →ₗ[ℚ]
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) Fᶜ (2 * p) :=
  Finsupp.linearCombination ℚ (schemeClosedRelativeGenerator X F d p hd)

theorem schemeClosedRelativeClassMap_single (x : schemeClosedSupportedPoint X F d) (r : ℚ) :
    schemeClosedRelativeClassMap X F d p hd (Finsupp.single x r) =
      r • schemeClosedRelativeGenerator X F d p hd x := Finsupp.linearCombination_single ℚ r x

variable (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))

def schemeClosedSupportedPoint_toOpen (x : schemeClosedSupportedPoint X F d) :
    schemeOpenSupportedPoint X U (Subtype.val ⁻¹' F) d :=
  ⟨x.val, fun _ hx => x.property hx⟩

def schemeClosedSupportedCycle_toOpen : schemeClosedSupportedCycle X F d →ₗ[ℚ]
    schemeOpenSupportedCycle X U (Subtype.val ⁻¹' F) d :=
  Finsupp.lmapDomain ℚ ℚ (schemeClosedSupportedPoint_toOpen X F d U)

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeClosedSupportedCycle_toOpen_forget (c : schemeClosedSupportedCycle X F d) :
    schemeOpenSupportedCycle_forget X U (Subtype.val ⁻¹' F) d (schemeClosedSupportedCycle_toOpen X F d U c) =
    schemeClosedSupportedCycle_forget X F d c := by
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ c) = Finsupp.mapDomain _ c
  rw [← Finsupp.mapDomain_comp]
  rfl

end

/-! The supported lift of the forgotten actual cycle recovers that cycle exactly. Hence a literal graded-cycle identity determines the same global supported class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (F : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (d p : ℕ)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeClosedRestrictCycle_forget (c : schemeClosedSupportedCycle X F d) :
    schemeClosedRestrictCycle X F d (schemeClosedSupportedCycle_forget X F d c) = c := by
  ext x
  exact schemeClosedSupportedCycle_forget_apply X F d c x

theorem schemeClosedRelativeClassMap_eq_of_forget_eq (c : schemeClosedSupportedCycle X F d)
    (b : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ)
    (he : schemeClosedSupportedCycle_forget X F d c = b) :
    schemeClosedRelativeClassMap X F d p hd c =
    schemeClosedRelativeClassMap X F d p hd (schemeClosedRestrictCycle X F d b) := by
  rw [← he, schemeClosedRestrictCycle_forget]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenSupportedCycle.BundleCycles

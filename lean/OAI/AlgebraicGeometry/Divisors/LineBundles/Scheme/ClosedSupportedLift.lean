import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenSupportedCycle
import OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction

/-! # Closed Supported Lift -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedSupportedLift.BundleCycles

noncomputable section

section

/-! Restriction of a global supported finite cycle class is the canonical local class of the same finite cycle on every analytic open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (F : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (d p : ℕ)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))

theorem schemeClosedRelativeGenerator_restrict (x : OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint X F d) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      Fᶜ U (2 * p) (OpenSupportedCycle.BundleCycles.schemeClosedRelativeGenerator X F d p hd x) =
    OpenSupportedCycle.BundleCycles.schemeOpenRelativeGenerator X U (Subtype.val ⁻¹' F) d p hd
      (OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint_toOpen X F d U x) := by
  let j := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
  let hx := OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint_mapsTo X F d x
  let hj : Set.MapsTo j (Subtype.val ⁻¹' F)ᶜ Fᶜ := fun _ hy => hy
  have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) j
    (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) hj hx (2 * p)
  have he := CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr (Category.comp_id j)
    (hx.comp hj) (OpenSupportedCycle.BundleCycles.schemeOpenSupportedPoint_mapsTo X U (Subtype.val ⁻¹' F) d
      (OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint_toOpen X F d U x)) (2 * p)
  exact ConcreteCategory.congr_hom (hc.trans he)
    (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X (irreducibleSetEquivPoints.symm x.val.val) p
      ((congrArg (fun n => n + p) x.val.property).trans hd))

theorem schemeClosedRelativeClassMap_restrict (c : OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle X F d) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      Fᶜ U (2 * p) (OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap X F d p hd c) =
    OpenSupportedCycle.BundleCycles.schemeOpenRelativeClassMap X U (Subtype.val ⁻¹' F) d p hd
      (OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_toOpen X F d U c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c e hc he => simp only [map_add, hc, he]
  | single x r =>
    have hs : OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_toOpen X F d U (Finsupp.single x r) =
        Finsupp.single (OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint_toOpen X F d U x) r := Finsupp.mapDomain_single
    rw [OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap_single, hs, OpenSupportedCycle.BundleCycles.schemeOpenRelativeClassMap_single, map_smul]
    exact congrArg (fun b => r • b) (schemeClosedRelativeGenerator_restrict X F d p hd U x)

end

/-! The actual coefficient condition gives a supported lift of the full graded cycle. Its restrictions keep precisely the original coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (F : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (d : ℕ)

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeClosed_forget_restrictCycle (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ)
    (hc : ∀ D : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d, c D ≠ 0 →
      Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm D.val)) ⊆ F) :
    OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget X F d (OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle X F d c) = c := by
  classical
  ext D
  by_cases hD : Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm D.val)) ⊆ F
  · exact (OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget_apply X F d (OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle X F d c) ⟨D, hD⟩).trans rfl
  · have hz : c D = 0 := by
      by_contra hn
      exact hD (hc D hn)
    rw [hz]
    exact Finsupp.mapDomain_of_notMem_range (OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle X F d c) D (by
      rintro ⟨E, he⟩
      exact hD (he ▸ E.property))

variable (p : ℕ) (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))

theorem schemeClosedRestrictedClass_eq_localClass (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ)
    (hc : ∀ D : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d, c D ≠ 0 →
      Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm D.val)) ⊆ F) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      Fᶜ U (2 * p) (OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap X F d p hd (OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle X F d c)) =
    OpenSupportedCycle.BundleCycles.schemeOpenRelativeClassMap X U (Subtype.val ⁻¹' F) d p hd
      (OpenSupportedCycle.BundleCycles.schemeOpenRestrictCycle X U (Subtype.val ⁻¹' F) d c) := by
  rw [schemeClosedRelativeClassMap_restrict]
  apply OpenSupportedCycle.BundleCycles.schemeOpenRelativeClassMap_eq_restrict_of_local_coefficients X U (Subtype.val ⁻¹' F) d p hd
  intro D _
  rw [OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_toOpen_forget, schemeClosed_forget_restrictCycle X F d c hc]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedSupportedLift.BundleCycles

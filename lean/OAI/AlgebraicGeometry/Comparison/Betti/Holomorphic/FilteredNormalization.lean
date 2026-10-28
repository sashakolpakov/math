import OAI.AlgebraicGeometry.Comparison.Betti.TruncatedNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DeRham
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredDerivedImage

/-! # Filtered Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredNormalization

noncomputable section

section

/-! The preserved holomorphic-to-Betti comparison identifies the actual truncation class with its original smooth derived representative. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]

local instance : StronglyLocallyContractibleSpace (Betti.Scheme.schemePointSpace X) :=
  AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace
    (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

local instance : MetrizableSpace (Betti.Scheme.schemePointSpace X) :=
  inferInstanceAs (MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))

theorem analyticConstantBettiIso_down (n : ℕ) (a : Analytic.De.analyticConstantCohomology X n) :
    Derived.DerivedSheafBetti.singularDerivedConstantLinearEquiv (Betti.Scheme.schemePointSpace X) n
      (Betti.Smooth.ReferenceCongruence.bettiDownEquiv X n ((Algebraic.Map.analyticConstantBettiIso X n).hom a)) = a := by
  change Derived.DerivedSheafBetti.singularDerivedConstantLinearEquiv (Betti.Scheme.schemePointSpace X) n
    ((Derived.DerivedSheafBetti.singularDerivedConstantLinearEquiv (Betti.Scheme.schemePointSpace X) n).symm a) = a
  exact LinearEquiv.apply_symm_apply _ a

theorem holomorphicBettiCohomologyIso_derivedClass (n : ℕ)
    (a : Hypercohomology.analyticHolomorphicCohomology X n) :
    Derived.DerivedSheafBetti.singularDerivedConstantLinearEquiv (Betti.Scheme.schemePointSpace X) n
      (Betti.Smooth.ReferenceCongruence.bettiDownEquiv X n ((DeRham.holomorphicBettiCohomologyIso X n).hom a)) ≫
        (Analytic.De.analyticDeRhamResolutionIso X).hom⟦(n : ℤ)⟧' =
      a ≫ (IntQuasiIso.derivedHolomorphicSmoothIso X).hom⟦(n : ℤ)⟧' := by
  change Derived.DerivedSheafBetti.singularDerivedConstantLinearEquiv (Betti.Scheme.schemePointSpace X) n
    (Betti.Smooth.ReferenceCongruence.bettiDownEquiv X n ((Algebraic.Map.analyticConstantBettiIso X n).hom
      ((Hypercohomology.holomorphicConstantCohomologyIso X n).hom a))) ≫ _ = _
  rw [analyticConstantBettiIso_down, Hypercohomology.holomorphicConstantCohomologyIso_apply]
  change (a ≫ ((IntQuasiIso.derivedHolomorphicSmoothIso X).hom ≫
    (Analytic.De.analyticDeRhamResolutionIso X).inv)⟦(n : ℤ)⟧') ≫
      (Analytic.De.analyticDeRhamResolutionIso X).hom⟦(n : ℤ)⟧' = _
  erw [Functor.map_comp, Category.assoc, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem holomorphicTruncationClass_smooth (n : ℕ) (r : ℤ)
    (a : TruncatedNaturality.holomorphicTruncatedCohomology X n r) :
    TruncatedNaturality.holomorphicTruncationClass X n r a ≫ (IntQuasiIso.derivedHolomorphicSmoothIso X).hom⟦(n : ℤ)⟧' =
      a ≫ (FilteredDerivedImage.Hodge.holomorphicTruncationToSmoothDerived
        (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) r)⟦(n : ℤ)⟧' := by
  change (a ≫ (DerivedCategory.Q.map (TruncatedNaturality.holomorphicTruncationInclusionInt X r))⟦(n : ℤ)⟧') ≫
    (DerivedCategory.Q.map (Int.holomorphicSmoothSheafMapInt X))⟦(n : ℤ)⟧' = _
  rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 3
  exact (HomologicalComplex.extendMap_comp _ _ (ComplexShape.embeddingUpIntGE 0)).symm

end

/-! Membership in the original holomorphic truncation image is detected by its actual Betti class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]

local instance : StronglyLocallyContractibleSpace (Betti.Scheme.schemePointSpace X) :=
  AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace
    (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local instance : MetrizableSpace (Betti.Scheme.schemePointSpace X) :=
  inferInstanceAs (MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))

theorem holomorphicBettiCohomologyIso_truncation_image_iff (n : ℕ) (r : ℤ)
    (b : Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X n) :
    (∃ c : TruncatedNaturality.holomorphicTruncatedCohomology X n r,
      Betti.Smooth.ReferenceCongruence.bettiDownEquiv X n ((DeRham.holomorphicBettiCohomologyIso X n).hom
        (TruncatedNaturality.holomorphicTruncationClass X n r c)) = b) ↔
    ∃ c : TruncatedNaturality.holomorphicTruncatedCohomology X n r,
      c ≫ (FilteredDerivedImage.Hodge.holomorphicTruncationToSmoothDerived
        (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) r)⟦(n : ℤ)⟧' =
      Derived.DerivedSheafBetti.singularDerivedConstantLinearEquiv (Betti.Scheme.schemePointSpace X) n b ≫
        (Analytic.De.analyticDeRhamResolutionIso X).hom⟦(n : ℤ)⟧' := by
  let e := Derived.DerivedSheafBetti.singularDerivedConstantLinearEquiv (Betti.Scheme.schemePointSpace X) n
  let u := (Analytic.De.analyticDeRhamResolutionIso X).hom⟦(n : ℤ)⟧'
  have hi : Function.Injective (fun b => e b ≫ u) := by
    intro b c h
    apply e.injective
    exact (cancel_mono u).mp h
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    exact (holomorphicTruncationClass_smooth X n r c).symm.trans
      ((holomorphicBettiCohomologyIso_derivedClass X n (TruncatedNaturality.holomorphicTruncationClass X n r c)).symm.trans
        (congrArg (fun b => e b ≫ u) hc))
  · rintro ⟨c, hc⟩
    refine ⟨c, hi ?_⟩
    exact (holomorphicBettiCohomologyIso_derivedClass X n (TruncatedNaturality.holomorphicTruncationClass X n r c)).trans
      ((holomorphicTruncationClass_smooth X n r c).trans hc)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredNormalization

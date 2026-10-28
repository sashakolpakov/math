import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexAugmentation
import OAI.Analysis.DifferentialForms.Manifold.DeRhamResolution

/-! # Smooth Simplex Sheaf Augmentation -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexSheafAugmentation

noncomputable section

/-!
# Actual degree-zero integration and the constant-sheaf augmentation

The degree-zero map is built from the genuine Duffy integral on each open
manifold. It respects restrictions by actual pullback naturality. Passing to
the established smooth singular sheaf and precomposing the proved standard
constant-sheaf identification gives the precise augmentation square.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace
open scoped Simplicial _root_.Manifold ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Actual integration in degree zero commutes with open restriction. -/
theorem smoothSimplexOpenZeroIntegration_restrict {U V : Opens M} (h : U ≤ V)
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E V 0) :
    SmoothSimplexAugmentation.smoothSimplexOpenZeroIntegration E U (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h form) =
      (Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothOpenRestriction E M (ModuleCat.of ℂ ℂ) (homOfLE h)).f 0
        (SmoothSimplexAugmentation.smoothSimplexOpenZeroIntegration E V form) := by
  apply (Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
    (ModuleCat.of ℂ ℂ) 0).toLinearEquiv.injective
  funext sigma
  change (Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
      (ModuleCat.of ℂ ℂ) 0).hom
        (SmoothSimplexAugmentation.smoothSimplexOpenZeroIntegration E U (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h form))
        sigma =
    (Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet
      (ModuleCat.of ℂ ℂ) 0).hom
        ((Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ)
          (Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothSingularMap E E (Opens.inclusion h)
            (contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) h))).f 0
            (SmoothSimplexAugmentation.smoothSimplexOpenZeroIntegration E V form)) sigma
  rw [SmoothSimplexAugmentation.smoothSimplexOpenZeroIntegration_evaluation, Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback,
    SmoothSimplexAugmentation.smoothSimplexOpenZeroIntegration_evaluation]
  change SmoothSimplexIntegration.smoothSimplexIntegration sigma
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U 0 (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h form)) =
    SmoothSimplexIntegration.smoothSimplexIntegration
      ((Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothSingularMap E E (Opens.inclusion h)
        (contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) h)).app _ sigma)
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E V 0 form)
  rw [Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_restrict, SmoothSimplexIntegration.smoothSimplexIntegration_postcompose]

variable (E M)

/-- The degree-zero natural transformation consists of the actual local integrals. -/
def smoothSimplexZeroPresheafMap :
    Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf E M 0 ⟶
      (Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).X 0 where
  app U := ModuleCat.ofHom (SmoothSimplexAugmentation.smoothSimplexOpenZeroIntegration E U.unop)
  naturality U V i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro form
    exact smoothSimplexOpenZeroIntegration_restrict (leOfHom i.unop) form

/-- Integration carries the actual locally constant inclusion to the actual
smooth singular augmentation as a natural transformation. -/
theorem smoothSimplexZeroPresheafMap_augmentation :
    Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroPresheaf E M ≫ smoothSimplexZeroPresheafMap E M =
      Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothAugmentation E M := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  exact SmoothSimplexAugmentation.smoothSimplexOpenZeroIntegration_augmentation U.unop

/-- Genuine degree-zero integration followed by the actual sheafification unit. -/
def smoothSimplexZeroSheafMap :
    (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M).X 0 ⟶
      (Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ)).X 0 :=
  ObjectProperty.homMk (smoothSimplexZeroPresheafMap E M ≫
    CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of M))
      ((Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).X 0))

/-- The locally constant sheaf augmentation square commutes for the actual integral. -/
theorem smoothSimplexZeroSheafMap_augmentation :
    Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E M ≫ smoothSimplexZeroSheafMap E M =
      Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothSheafAugmentation E M := by
  apply CategoryTheory.Sheaf.hom_ext
  change Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroPresheaf E M ≫
      (smoothSimplexZeroPresheafMap E M ≫
        CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of M))
          ((Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).X 0)) = _
  rw [Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothSheafAugmentation_hom, ← Category.assoc,
    smoothSimplexZeroPresheafMap_augmentation]

/-- The same square for mathlib's standard constant complex sheaf, using its
proved identification with locally constant sections. -/
theorem smoothSimplexZeroSheafMap_constant_augmentation :
    Analysis.DifferentialForms.Manifold.DeRhamResolution.manifoldConstantToDeRham E M ≫ smoothSimplexZeroSheafMap E M =
      (Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn (TopCat.of M)).hom ≫
        Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothSheafAugmentation E M := by
  change ((Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn (TopCat.of M)).hom ≫
    Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E M) ≫ smoothSimplexZeroSheafMap E M = _
  exact (Category.assoc (Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn (TopCat.of M)).hom
      (Analysis.DifferentialForms.Manifold.LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E M) (smoothSimplexZeroSheafMap E M)).trans
    (congrArg (fun map => (Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn (TopCat.of M)).hom ≫ map)
      (smoothSimplexZeroSheafMap_augmentation E M))

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexSheafAugmentation

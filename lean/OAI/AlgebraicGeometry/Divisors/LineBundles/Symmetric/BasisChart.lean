import OAI.AlgebraicGeometry.Divisors.LineBundles.BasisCoordinateSplit
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineCompactification
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Base

/-! # Basis Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisChart.BundleCycles

noncomputable section

/-! Splitting a basis coordinate realizes the corresponding projective
chart as the actual affine symmetric spectrum of the other coordinates. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (b : Module.Basis ι R M) (i : ι)

def symmetricBasisChartMap :
    Spec (.of (SymmetricAlgebra R ({j : ι // j ≠ i} → R))) ⟶ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M :=
  AffineCompactification.BundleCycles.symmetricAffineCompactification R ({j : ι // j ≠ i} → R) ≫
    (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso (BasisCoordinateSplit.BundleCycles.basisCoordinateSplit b i)).inv

instance symmetricBasisChartMap_isOpenImmersion : IsOpenImmersion (symmetricBasisChartMap b i) := by
  unfold symmetricBasisChartMap
  infer_instance

theorem symmetricBasisChartMap_over :
    symmetricBasisChartMap b i ≫ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M =
      Spec.map (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R ({j : ι // j ≠ i} → R)))) := by
  change (AffineCompactification.BundleCycles.symmetricAffineCompactification R ({j : ι // j ≠ i} → R) ≫
    SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveMap (BasisCoordinateSplit.BundleCycles.basisCoordinateSplit b i).toLinearMap (BasisCoordinateSplit.BundleCycles.basisCoordinateSplit b i).surjective) ≫ _ = _
  rw [Category.assoc, SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over, AffineCompactification.BundleCycles.symmetricAffineCompactification_over]

theorem symmetricBasisChartMap_opensRange :
    (symmetricBasisChartMap b i).opensRange =
      Proj.basicOpen (Grading.BundleCycles.symmetricGrading R M) (SymmetricAlgebra.ι R M (b i)) := by
  let e := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso (BasisCoordinateSplit.BundleCycles.basisCoordinateSplit b i)
  have hp : e.inv ⁻¹ᵁ Proj.basicOpen (Grading.BundleCycles.symmetricGrading R M) (SymmetricAlgebra.ι R M (b i)) =
      Proj.basicOpen (Grading.BundleCycles.symmetricGrading R (R × ({j : ι // j ≠ i} → R)))
        (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R ({j : ι // j ≠ i} → R)) := by
    change Proj.map (GradedMap.BundleCycles.symmetricGradedMap (BasisCoordinateSplit.BundleCycles.basisCoordinateSplit b i).toLinearMap) _ ⁻¹ᵁ _ = _
    rw [Proj.map_preimage_basicOpen, GradedMap.BundleCycles.symmetricGradedMap_generator]
    exact congrArg (fun v => Proj.basicOpen _ (SymmetricAlgebra.ι R _ v)) (BasisCoordinateSplit.BundleCycles.basisCoordinateSplit_basis b i)
  change (AffineCompactification.BundleCycles.symmetricAffineCompactification R ({j : ι // j ≠ i} → R) ≫ e.inv).opensRange = _
  rw [Scheme.Hom.opensRange_comp, AffineCompactification.BundleCycles.symmetricAffineCompactification_opensRange, ← hp]
  apply TopologicalSpace.Opens.ext
  exact Set.image_preimage_eq (f := e.inv)
    (↑(Proj.basicOpen (Grading.BundleCycles.symmetricGrading R M) (SymmetricAlgebra.ι R M (b i))) : Set (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M))
    (show Function.Surjective e.inv from e.inv.homeomorph.surjective)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisChart.BundleCycles

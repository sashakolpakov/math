import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisAffineChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Inclusion

/-! # Basis Hyperplane -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisHyperplane.BundleCycles

noncomputable section

/-! Each basis affine chart has an actual closed complementary
projective hyperplane, obtained from the quotient by that basis coordinate. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (b : Module.Basis ι R M) (i : ι)

def symmetricBasisHyperplaneMap :
    SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R ({j : ι // j ≠ i} → R) ⟶ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M :=
  SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R ({j : ι // j ≠ i} → R) ≫
    (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso (BasisCoordinateSplit.BundleCycles.basisCoordinateSplit b i)).inv

instance symmetricBasisHyperplaneMap_isClosedImmersion :
    IsClosedImmersion (symmetricBasisHyperplaneMap b i) := by
  unfold symmetricBasisHyperplaneMap
  infer_instance

theorem symmetricBasisHyperplaneMap_over :
    symmetricBasisHyperplaneMap b i ≫ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M =
      SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R ({j : ι // j ≠ i} → R) := by
  change (SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R ({j : ι // j ≠ i} → R) ≫
    SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveMap (BasisCoordinateSplit.BundleCycles.basisCoordinateSplit b i).toLinearMap (BasisCoordinateSplit.BundleCycles.basisCoordinateSplit b i).surjective) ≫ _ = _
  rw [Category.assoc, SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over]
  exact SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over (LinearMap.snd R R ({j : ι // j ≠ i} → R)) _

theorem symmetricBasisHyperplaneMap_range :
    Set.range (symmetricBasisHyperplaneMap b i) = (Set.range (BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap b i))ᶜ := by
  classical
  let e := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso (BasisCoordinateSplit.BundleCycles.basisCoordinateSplit b i)
  have hj : Set.range (BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap b i) =
      e.inv '' Set.range (AffineCompactification.BundleCycles.symmetricAffineCompactification R ({j : ι // j ≠ i} → R)) := by
    change (↑(BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap b i).opensRange : Set (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M)) = _
    unfold BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap
    rw [Scheme.Hom.opensRange_comp_of_isIso]
    change Set.range (e.inv ∘ AffineCompactification.BundleCycles.symmetricAffineCompactification R ({j : ι // j ≠ i} → R)) = _
    exact Set.range_comp _ _
  change Set.range (e.inv ∘ SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R ({j : ι // j ≠ i} → R)) = _
  rw [Set.range_comp, SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion_range, hj]
  exact Set.image_compl_eq e.inv.homeomorph.bijective

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisHyperplane.BundleCycles

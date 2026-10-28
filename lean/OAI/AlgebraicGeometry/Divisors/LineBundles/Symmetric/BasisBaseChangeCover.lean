import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisAffineChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceBase
import OAI.AlgebraicGeometry.Divisors.LineBundles.PullbackRange

/-! # Basis Base Change Cover -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisBaseChangeCover.BundleCycles

noncomputable section

/-! The actual basis charts of symmetric Proj give a relative
affine-space open cover after every scheme base change. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (b : Module.Basis ι R M) {Y : Scheme.{0}} (g : Y ⟶ Spec (.of R))

def symmetricBasisBaseChangeChartMap (i : ι) :
    AffineSpace {j : ι // j ≠ i} (pullback g (𝟙 _)) ⟶ pullback (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) g :=
  LineBundles.AffineSpace.SourceBase.BundleCycles.affineSpaceSourceBaseChangeMap (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) g (𝟙 _) {j : ι // j ≠ i}
    (BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap b i) (by rw [Category.comp_id]; exact (BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap_over b i).symm)

theorem symmetricBasisBaseChangeChart_isPullback (i : ι) :
    IsPullback (symmetricBasisBaseChangeChartMap b g i)
      (AffineSpace.map {j : ι // j ≠ i} (pullback.snd g (𝟙 _)))
      (pullback.fst (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) g) (BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap b i) :=
  LineBundles.AffineSpace.SourceBase.BundleCycles.affineSpaceSourceBaseChange_isPullback _ _ _ _ _ _

instance symmetricBasisBaseChangeChart_isOpenImmersion (i : ι) :
    IsOpenImmersion (symmetricBasisBaseChangeChartMap b g i) :=
  MorphismProperty.of_isPullback (symmetricBasisBaseChangeChart_isPullback b g i).flip
    (BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap_isOpenImmersion b i)

theorem symmetricBasisBaseChangeChart_range (i : ι) :
    Set.range (symmetricBasisBaseChangeChartMap b g i) =
      (pullback.fst (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) g) ⁻¹'
        (↑(Proj.basicOpen (Grading.BundleCycles.symmetricGrading R M) (SymmetricAlgebra.ι R M (b i))) : Set (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M)) :=
  (PullbackRange.BundleCycles.range_of_isPullback (symmetricBasisBaseChangeChart_isPullback b g i)).trans
    (congrArg (fun s => (pullback.fst (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) g) ⁻¹' s)
      (congrArg (fun U : (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M).Opens => (U : Set (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M)))
        (BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap_opensRange b i)))

def symmetricBasisBaseChangeCover : (pullback (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) g).OpenCover :=
  Scheme.Cover.mkOfCovers _ (fun i => AffineSpace {j : ι // j ≠ i} (pullback g (𝟙 _)))
    (symmetricBasisBaseChangeChartMap b g) (fun z => by
      obtain ⟨i, a, ha⟩ := (BasisCover.BundleCycles.symmetricBasisCover b).openCover.exists_eq (pullback.fst (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) g z)
      refine ⟨i, (Set.ext_iff.mp (symmetricBasisBaseChangeChart_range b g i) z).mpr ?_⟩
      change pullback.fst (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) g z ∈
        (↑(Proj.basicOpen (Grading.BundleCycles.symmetricGrading R M) (SymmetricAlgebra.ι R M (b i))) : Set (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M))
      rw [← ha, ← BasisCover.BundleCycles.symmetricBasisCover_opensRange b i]
      exact Set.mem_range_self a)
    (symmetricBasisBaseChangeChart_isOpenImmersion b g)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisBaseChangeCover.BundleCycles

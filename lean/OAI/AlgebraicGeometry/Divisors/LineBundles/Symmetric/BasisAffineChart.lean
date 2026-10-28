import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisCover
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineSchemeIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceRank

/-! # Basis Affine Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisAffineChart.BundleCycles

noncomputable section

/-! Actual affine-space charts for the projective symmetric spectrum
of a finite free module. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (b : Module.Basis ι R M) (i : ι)

def symmetricBasisAffineChartMap :
    AffineSpace {j : ι // j ≠ i} (Spec (.of R)) ⟶ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M := by
  classical
  exact (AffineSchemeIso.BundleCycles.symmetricAffineSchemeIso (Pi.basisFun R {j : ι // j ≠ i})).inv ≫ BasisChart.BundleCycles.symmetricBasisChartMap b i

instance symmetricBasisAffineChartMap_isOpenImmersion : IsOpenImmersion (symmetricBasisAffineChartMap b i) := by
  classical
  unfold symmetricBasisAffineChartMap
  infer_instance

theorem symmetricBasisAffineChartMap_over :
    symmetricBasisAffineChartMap b i ≫ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M =
      (AffineSpace {j : ι // j ≠ i} (Spec (.of R)) ↘ Spec (.of R)) := by
  classical
  unfold symmetricBasisAffineChartMap
  rw [Category.assoc, BasisChart.BundleCycles.symmetricBasisChartMap_over, ← AffineSchemeIso.BundleCycles.symmetricAffineSchemeIso_over (Pi.basisFun R {j : ι // j ≠ i}),
    Iso.inv_hom_id_assoc]

theorem symmetricBasisAffineChartMap_opensRange :
    (symmetricBasisAffineChartMap b i).opensRange =
      Proj.basicOpen (Grading.BundleCycles.symmetricGrading R M) (SymmetricAlgebra.ι R M (b i)) := by
  classical
  unfold symmetricBasisAffineChartMap
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (BasisChart.BundleCycles.symmetricBasisChartMap_opensRange b i)

include b in
theorem symmetricProjective_hasAffineSpaceSourceChartsOfRank :
    LineBundles.AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) (Nat.card ι - 1) := by
  classical
  intro x
  obtain ⟨i, y, rfl⟩ := (BasisCover.BundleCycles.symmetricBasisCover b).openCover.exists_eq x
  refine ⟨Spec (.of R), 𝟙 _, {j : ι // j ≠ i}, inferInstance, symmetricBasisAffineChartMap b i,
    inferInstance, symmetricBasisAffineChartMap_isOpenImmersion b i, ?_, ?_, ?_⟩
  · have hr : Set.range ((BasisCover.BundleCycles.symmetricBasisCover b).f i) = Set.range (symmetricBasisAffineChartMap b i) :=
      congrArg (fun U : (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M).Opens => (U : Set (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M)))
        ((BasisCover.BundleCycles.symmetricBasisCover_opensRange b i).trans (symmetricBasisAffineChartMap_opensRange b i).symm)
    exact hr ▸ Set.mem_range_self y
  · rw [Category.comp_id]
    exact (symmetricBasisAffineChartMap_over b i).symm
  · let : Unique {j : ι // j = i} := ⟨⟨i, rfl⟩, fun j => Subtype.ext j.property⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_unique (α := {j : ι // j = i})]

include b in
theorem symmetricProjective_hasAffineSpaceSourceCharts :
    LineBundles.AffineSpace.SourceBase.BundleCycles.HasAffineSpaceSourceCharts (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M) :=
  (symmetricProjective_hasAffineSpaceSourceChartsOfRank b).forget

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisAffineChart.BundleCycles

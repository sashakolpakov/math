import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.DeformationPunctured
import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.DivisorPullback

/-! # Punctured Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PuncturedCycle.BundleCycles

noncomputable section

/-! The genuine punctured fiber generic points and their complete cycle extension commute with open restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] (I : Y.IdealSheafData)

theorem globalOpenPuncturedMap_genericPoint (x : X) :
    DeformationPunctured.BundleCycles.globalOpenPuncturedMap i I (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint (I.comap i) x) =
      Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint I (i x) := by
  let j := DeformationPunctured.BundleCycles.globalOpenPuncturedMap i I
  have h := DeformationPunctured.BundleCycles.globalOpenPuncturedMap_projection i I
  have hp : Punctured.DeformationCharts.BundleCycles.puncturedDeformationProjection I (j (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint (I.comap i) x)) = i x :=
    (congrArg (fun k => k (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint (I.comap i) x)) h).trans
      (congrArg i (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint_projection (I.comap i) x))
  have hs := Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint_specializes I (i x) (j (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint (I.comap i) x)) hp
  have hm : Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint I (i x) ∈ j.opensRange :=
    hs.mem_open j.opensRange.isOpen ⟨Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint (I.comap i) x, rfl⟩
  obtain ⟨a, ha⟩ := hm
  have hqa : Punctured.DeformationCharts.BundleCycles.puncturedDeformationProjection (I.comap i) a = x := by
    apply i.isOpenEmbedding.injective
    exact (congrArg (fun k => k a) h).symm.trans
      ((congrArg (Punctured.DeformationCharts.BundleCycles.puncturedDeformationProjection I) ha).trans (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint_projection I (i x)))
  have ht := (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint_specializes (I.comap i) x a hqa).map j.continuous
  exact ((congrArg (fun y => j (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint (I.comap i) x) ⤳ y) ha).mp ht).antisymm hs |>.eq

theorem puncturedCycleExtension_open (z : Y →₀ ℚ) :
    Finsupp.comapDomain (DeformationPunctured.BundleCycles.globalOpenPuncturedMap i I) (Punctured.DivisorPullback.BundleCycles.puncturedCycleExtension I z)
      (DeformationPunctured.BundleCycles.globalOpenPuncturedMap i I).isOpenEmbedding.injective.injOn =
      Punctured.DivisorPullback.BundleCycles.puncturedCycleExtension (I.comap i) (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn) := by
  ext a
  change Finsupp.mapDomain (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint I) z (DeformationPunctured.BundleCycles.globalOpenPuncturedMap i I a) =
    Finsupp.mapDomain (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint (I.comap i))
      (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn) a
  by_cases ha : a ∈ Set.range (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint (I.comap i))
  · obtain ⟨x, rfl⟩ := ha
    rw [globalOpenPuncturedMap_genericPoint,
      Finsupp.mapDomain_apply_of_injective (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint_injective I),
      Finsupp.mapDomain_apply_of_injective (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint_injective (I.comap i))]
    rfl
  · have hj : DeformationPunctured.BundleCycles.globalOpenPuncturedMap i I a ∉ Set.range (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint I) := by
      rintro ⟨y, hy⟩
      have hb : i (Punctured.DeformationCharts.BundleCycles.puncturedDeformationProjection (I.comap i) a) = y :=
        (congrArg (fun k => k a) (DeformationPunctured.BundleCycles.globalOpenPuncturedMap_projection i I)).symm.trans
          ((congrArg (Punctured.DeformationCharts.BundleCycles.puncturedDeformationProjection I) hy.symm).trans (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint_projection I y))
      have he := globalOpenPuncturedMap_genericPoint i I (Punctured.DeformationCharts.BundleCycles.puncturedDeformationProjection (I.comap i) a)
      rw [hb] at he
      exact ha ⟨_, (DeformationPunctured.BundleCycles.globalOpenPuncturedMap i I).isOpenEmbedding.injective (he.trans hy)⟩
    rw [Finsupp.mapDomain_of_notMem_range _ _ hj, Finsupp.mapDomain_of_notMem_range _ _ ha]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PuncturedCycle.BundleCycles

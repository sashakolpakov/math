import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceBase
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceRank

/-! # Charts Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

section

/-! Relative affine-space charts on the source persist over arbitrary
base changes, including singular closed supports. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem AffineSpace.SourceBase.BundleCycles.HasAffineSpaceSourceCharts.baseChange {E X Y : Scheme.{0}} {p : E ⟶ X}
    (h : AffineSpace.SourceBase.BundleCycles.HasAffineSpaceSourceCharts p) (g : Y ⟶ X) :
    AffineSpace.SourceBase.BundleCycles.HasAffineSpaceSourceCharts (pullback.snd p g) := by
  intro z
  obtain ⟨U, i, ι, hι, j, hi, hj, hz, hs⟩ := h (pullback.fst p g z)
  let := hi
  let := hj
  obtain ⟨a, ha⟩ := hz
  refine ⟨pullback g i, pullback.fst g i, ι, hι,
    AffineSpace.SourceBase.BundleCycles.affineSpaceSourceBaseChangeMap p g i ι j hs, inferInstance, inferInstance, ?_,
    (AffineSpace.SourceBase.BundleCycles.affineSpaceSourceBaseChangeMap_snd p g i ι j hs).symm⟩
  obtain ⟨b, hb, _⟩ := Scheme.exists_preimage_of_isPullback
    (AffineSpace.SourceBase.BundleCycles.affineSpaceSourceBaseChange_isPullback p g i ι j hs) z a ha.symm
  exact ⟨b, hb⟩

theorem AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank.baseChange {E X Y : Scheme.{0}} {p : E ⟶ X} {r : ℕ}
    (h : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (g : Y ⟶ X) :
    AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (pullback.snd p g) r := by
  intro z
  obtain ⟨U, i, ι, hι, j, hi, hj, hz, hs, hr⟩ := h (pullback.fst p g z)
  let := hi
  let := hj
  obtain ⟨a, ha⟩ := hz
  refine ⟨pullback g i, pullback.fst g i, ι, hι,
    AffineSpace.SourceBase.BundleCycles.affineSpaceSourceBaseChangeMap p g i ι j hs, inferInstance, inferInstance, ?_,
    (AffineSpace.SourceBase.BundleCycles.affineSpaceSourceBaseChangeMap_snd p g i ι j hs).symm, hr⟩
  obtain ⟨b, hb, _⟩ := Scheme.exists_preimage_of_isPullback
    (AffineSpace.SourceBase.BundleCycles.affineSpaceSourceBaseChange_isPullback p g i ι j hs) z a ha.symm
  exact ⟨b, hb⟩

end

/-! Affine source charts transfer through actual scheme isomorphisms
and arbitrary specified pullback squares. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank.isoSource {E X E' : Scheme.{0}}
    {p : E ⟶ X} {r : ℕ} (h : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (e : E' ≅ E) :
    AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (e.hom ≫ p) r := by
  intro z
  obtain ⟨U, i, ι, hι, j, hi, hj, hz, hs, hr⟩ := h (e.hom z)
  let := hι
  let := hi
  let := hj
  refine ⟨U, i, ι, hι, j ≫ e.inv, inferInstance, inferInstance, ?_, ?_, hr⟩
  · obtain ⟨a, ha⟩ := hz
    refine ⟨a, ?_⟩
    change e.inv (j a) = z
    rw [ha]
    exact congrArg (fun k : E' ⟶ E' => k z) e.hom_inv_id
  · rw [Category.assoc, e.inv_hom_id_assoc]
    exact hs

theorem AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank.of_isPullback {E X E' U : Scheme.{0}}
    {p : E ⟶ X} {r : ℕ} (h : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)
    (q : E' ⟶ U) (i : U ⟶ X) (j : E' ⟶ E) (hs : IsPullback q j i p) :
    AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r := by
  have H := (h.baseChange i).isoSource hs.flip.isoPullback
  rwa [hs.flip.isoPullback_hom_snd] at H

end

end OAI.AlgebraicGeometry.Divisors.LineBundles

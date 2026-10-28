import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.OverMaps

/-! # Section Projective Identities -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionProjectiveIdentities

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u
variable {S : Scheme.{u}} {X Y : Over S}
  (L : Line.Bundles.LineBundle X.left) (M : Line.Bundles.LineBundle Y.left) {n m : ℕ}
  (s : Fin (n + 1) → (Line.Bundles.structureModule X.left ⟶ L.sheaf))
  (t : Fin (m + 1) → (Line.Bundles.structureModule Y.left ⟶ M.sheaf))
  (hs : ∀ x : X.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
  (ht : ∀ x : Y.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (t i))
abbrev externalFirstSectionProjectiveIdentity :=
  Section.OverMaps.sectionProjectiveOverMap_precomp (fst X Y) L s hs
    (Section.ChartArbitraryPullback.lineBundleSections_pullback_covers (fst X Y).left L s hs)
abbrev externalSecondSectionProjectiveIdentity :=
  Section.OverMaps.sectionProjectiveOverMap_precomp (snd X Y) M t ht
    (Section.ChartArbitraryPullback.lineBundleSections_pullback_covers (snd X Y).left M t ht)
abbrev externalPairSectionProjectiveIdentity :=
  Section.OverMaps.sectionProjectiveOverMap_pair_segre (X ⊗ Y)
    (L.pullback (fst X Y).left) (M.pullback (snd X Y).left)
    (fun i => Ample.LineBundles.pullbackSection (fst X Y).left (s i))
    (fun i => Ample.LineBundles.pullbackSection (snd X Y).left (t i))
    (Section.ChartArbitraryPullback.lineBundleSections_pullback_covers (fst X Y).left L s hs)
    (Section.ChartArbitraryPullback.lineBundleSections_pullback_covers (snd X Y).left M t ht)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionProjectiveIdentities

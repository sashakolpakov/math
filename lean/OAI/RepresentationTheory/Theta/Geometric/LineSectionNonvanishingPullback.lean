import OAI.RepresentationTheory.Theta.Geometric.NonvanishingScalarPullback

/-! # Line Section Nonvanishing Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.LineSectionNonvanishingPullback

noncomputable section

/-! Nonvanishing of a line-bundle section commutes with every scheme pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem lineSectionNonvanishing_pullback {X Y : Scheme} (f : X ⟶ Y)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L.sheaf) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) = f ⁻¹ᵁ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s := by
  ext x
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyTrivial (f x)
  let V := f ⁻¹ᵁ U
  have h : V.ι ⁻¹ᵁ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) =
      (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) := by
    calc
      _ = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection V.ι (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s)) :=
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback V.ι _).symm
      _ = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (V.ι ≫ f) s) :=
        NonvanishingFunctorComparison.sectionNonvanishing_pullback_comp V.ι f s
      _ = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection ((f ∣_ U) ≫ U.ι) s) :=
        congrArg (fun a => AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection a s)) (morphismRestrict_ι f U).symm
      _ = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (f ∣_ U) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s)) :=
        (NonvanishingFunctorComparison.sectionNonvanishing_pullback_comp (f ∣_ U) U.ι s).symm
      _ = (f ∣_ U) ⁻¹ᵁ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) :=
        NonvanishingScalarPullback.sectionNonvanishing_pullback_framed (f ∣_ U) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) e
      _ = _ := congrArg (fun W => (f ∣_ U) ⁻¹ᵁ W) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback U.ι s)
  have hh := (congrArg (fun W : V.toScheme.Opens => (⟨x, hxU⟩ : V.toScheme) ∈ W) h).to_iff
  change x ∈ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) ↔
    U.ι ((f ∣_ U) (⟨x, hxU⟩ : V.toScheme)) ∈ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s at hh
  have hp := congrArg (fun a : V.toScheme ⟶ Y => a (⟨x, hxU⟩ : V.toScheme)) (morphismRestrict_ι f U)
  change U.ι ((f ∣_ U) (⟨x, hxU⟩ : V.toScheme)) = f x at hp
  rw [hp] at hh
  exact hh

end

end OAI.RepresentationTheory.Theta.Geometric.LineSectionNonvanishingPullback

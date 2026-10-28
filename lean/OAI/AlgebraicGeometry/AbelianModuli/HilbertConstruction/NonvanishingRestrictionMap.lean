import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.PullbackCoherence

/-! # Nonvanishing Restriction Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonvanishingRestrictionMap

noncomputable section

/-! Actual restriction maps between section nonvanishing subschemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {L : Y.Modules}

/-- Restrict an open immersion to the nonvanishing locus of a section. -/
def sectionNonvanishingMap (s : Line.Bundles.structureModule Y ⟶ L) :
    (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).toScheme ⟶ (Ample.LineBundles.sectionNonvanishing s).toScheme :=
  (X.isoOfEq (Section.Nonvanishing.sectionNonvanishing_pullback f s)).hom ≫ (f ∣_ Ample.LineBundles.sectionNonvanishing s)

instance sectionNonvanishingMap_openImmersion (s : Line.Bundles.structureModule Y ⟶ L) :
    IsOpenImmersion (sectionNonvanishingMap f s) := by
  change IsOpenImmersion ((X.isoOfEq (Section.Nonvanishing.sectionNonvanishing_pullback f s)).hom ≫
    (f ∣_ Ample.LineBundles.sectionNonvanishing s))
  infer_instance

theorem sectionNonvanishingMap_ι (s : Line.Bundles.structureModule Y ⟶ L) :
    sectionNonvanishingMap f s ≫ (Ample.LineBundles.sectionNonvanishing s).ι =
      (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι ≫ f := by
  simp only [sectionNonvanishingMap, Category.assoc, morphismRestrict_ι]
  rw [← Category.assoc, Scheme.isoOfEq_hom_ι]

/-- The restriction square of nonvanishing loci is a pullback. -/
theorem sectionNonvanishingMap_isPullback (s : Line.Bundles.structureModule Y ⟶ L) :
    IsPullback (sectionNonvanishingMap f s) (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι
      (Ample.LineBundles.sectionNonvanishing s).ι f := by
  apply IsOpenImmersion.isPullback
  · exact (sectionNonvanishingMap_ι f s).symm
  · rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
    exact (Section.Nonvanishing.sectionNonvanishing_pullback f s).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonvanishingRestrictionMap

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberSectionGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerSectionsAndVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange

/-! # Ample Fiber Power Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.AmpleFiberPowerSections

noncomputable section

/-! An ample residue fiber of a proper flat family has a positive power covered by actual global sections of the original family. Fiberwise ampleness gives such a section at every point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem properFlat_power_sections_cover_ample_fiber
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X) (x : S)
    (hL : (L.pullback (f.fiberι x)).IsAmple) :
    ∃ (d : ℕ) (_ : 0 < d), ∀ y : f.fiber x,
      ∃ s : Line.Bundles.structureModule X ⟶ (L.tensorPower d).sheaf,
        f.fiberι x y ∈ Ample.LineBundles.sectionNonvanishing s := by
  have hstable : MorphismProperty.IsStableUnderBaseChange
      (fun {Y Z : Scheme.{u}} (p : Y ⟶ Z) => IsProper p) := IsProper.isStableUnderBaseChange
  have hproper : IsProper (CategoryTheory.Limits.pullback.snd f (S.fromSpecResidueField x)) :=
    hstable.of_isPullback (CategoryTheory.IsPullback.of_hasPullback f
      (S.fromSpecResidueField x)) (inferInstanceAs (IsProper f))
  have : IsProper (f.fiberToSpecResidueField x) := hproper
  obtain ⟨d, hd, n, t, ht, hv⟩ := Ample.PowerSectionsAndVanishing.ample_exists_power_sections_and_vanishing
    (f.fiberToSpecResidueField x) (L.pullback (f.fiberι x)) hL
  let e := L.powerBaseChangeIso (f.fiberι x) d
  have : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H ((L.pullback (f.fiberι x)).tensorPower d).sheaf 1) :=
    hv 1 (by decide)
  have hH : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H ((L.tensorPower d).pullback (f.fiberι x)).sheaf 1) :=
    (ConcreteCategory.bijective_of_isIso
      ((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (f.fiber x) 1).map e.hom)).injective.subsingleton
  refine ⟨d, hd, FiberSectionGeneration.properFlat_global_sections_cover_fiber f (L.tensorPower d) x hH ?_⟩
  intro y
  obtain ⟨i, hi⟩ := ht y
  exact ⟨t i ≫ e.inv, (Ample.Powers.sectionNonvanishing_comp_iso (t i) e.symm).symm ▸ hi⟩

theorem properFlat_pointwise_power_sections_of_ample_fibers
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X)
    (hL : ∀ x : S, (L.pullback (f.fiberι x)).IsAmple) :
    ∀ y : X, ∃ (d : ℕ) (_ : 0 < d) (s : Line.Bundles.structureModule X ⟶ (L.tensorPower d).sheaf),
      y ∈ Ample.LineBundles.sectionNonvanishing s := by
  intro y
  have hr : y ∈ Set.range (f.fiberι (f y)) := by
    rw [f.range_fiberι (f y)]
    rfl
  obtain ⟨z, hz⟩ := hr
  obtain ⟨d, hd, hs⟩ := properFlat_power_sections_cover_ample_fiber f L (f y) (hL (f y))
  obtain ⟨s, hzs⟩ := hs z
  exact ⟨d, hd, s, (congrArg (fun w => w ∈ Ample.LineBundles.sectionNonvanishing s) hz).mp hzs⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.AmpleFiberPowerSections

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FrameTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSections

/-! # Section Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.SectionRestriction

noncomputable section

/-!
Sections for the concrete open-restriction functor, their component formulas,
and comparison with the canonical pullback construction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L M : Y.Modules}

/-- Restrict a section using the explicit structure-module frame of an open immersion. -/
def restrictSection (f : X ⟶ Y) [IsOpenImmersion f] (s : Line.Bundles.structureModule Y ⟶ L) :
    Line.Bundles.structureModule X ⟶ L.restrict f :=
  (Scheme.Modules.restrictUnitIso f).inv ≫ (Scheme.Modules.restrictFunctor f).map s

theorem restrictSection_app (f : X ⟶ Y) [IsOpenImmersion f]
    (s : Line.Bundles.structureModule Y ⟶ L) (U : X.Opens) (r : Γ(X, U)) :
    (restrictSection f s).app U r = s.app (f ''ᵁ U) ((f.appIso U).inv r) := rfl

theorem restrictSection_app_one (f : X ⟶ Y) [IsOpenImmersion f]
    (s : Line.Bundles.structureModule Y ⟶ L) (U : X.Opens) :
    (restrictSection f s).app U (1 : Γ(X, U)) = s.app (f ''ᵁ U) (1 : Γ(Y, f ''ᵁ U)) :=
  (restrictSection_app f s U 1).trans
    (congrArg (fun r : Γ(Y, f ''ᵁ U) => s.app (f ''ᵁ U) r) (map_one (f.appIso U).inv.hom))

theorem restrictSection_postcomp (f : X ⟶ Y) [IsOpenImmersion f]
    (s : Line.Bundles.structureModule Y ⟶ L) (a : L ⟶ M) :
    restrictSection f (s ≫ a) = restrictSection f s ≫ (Scheme.Modules.restrictFunctor f).map a := by
  exact (congrArg (fun z : (Line.Bundles.structureModule Y).restrict f ⟶ M.restrict f =>
    (Scheme.Modules.restrictUnitIso f).inv ≫ z) ((Scheme.Modules.restrictFunctor f).map_comp s a)).trans
      (Category.assoc _ _ _).symm

/-- Changing the structure-module frame does not change a section's nonvanishing open. -/
theorem sectionNonvanishing_sourceIso (a : Line.Bundles.structureModule Y ≅ Line.Bundles.structureModule Y)
    (s : Line.Bundles.structureModule Y ⟶ L) : Ample.LineBundles.sectionNonvanishing (a.hom ≫ s) = Ample.LineBundles.sectionNonvanishing s := by
  unfold Ample.LineBundles.sectionNonvanishing
  apply congrArg sSup
  ext U
  change IsIso (Ample.LineBundles.pullbackSection U.ι (a.hom ≫ s)) ↔ IsIso (Ample.LineBundles.pullbackSection U.ι s)
  rw [Nonvanishing.isIso_pullbackSection_iff, Nonvanishing.isIso_pullbackSection_iff, Functor.map_comp, isIso_comp_left_iff]

/-- Explicit restriction pulls back the section's nonvanishing locus. -/
theorem sectionNonvanishing_restrictSection (f : X ⟶ Y) [IsOpenImmersion f]
    (s : Line.Bundles.structureModule Y ⟶ L) : Ample.LineBundles.sectionNonvanishing (restrictSection f s) =
      f ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing s := by
  let e := Scheme.Modules.restrictFunctorIsoPullback f
  let a := (Line.Bundles.structureModulePullbackIso f).symm ≪≫ e.symm.app (Line.Bundles.structureModule Y) ≪≫
    Scheme.Modules.restrictUnitIso f
  have h : (a.hom ≫ restrictSection f s) ≫ (e.app L).hom = Ample.LineBundles.pullbackSection f s :=
    Frame.Comparison.framedSection_functorComparison (Scheme.Modules.restrictFunctor f) (Scheme.Modules.pullback f)
      e (Scheme.Modules.restrictUnitIso f) (Line.Bundles.structureModulePullbackIso f) s
  have hd : Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s) = Ample.LineBundles.sectionNonvanishing (restrictSection f s) :=
    (congrArg (fun t => Ample.LineBundles.sectionNonvanishing t) h).symm.trans
      ((Ample.Powers.sectionNonvanishing_comp_iso (a.hom ≫ restrictSection f s) (e.app L)).trans
        (sectionNonvanishing_sourceIso a (restrictSection f s)))
  exact hd.symm.trans (Nonvanishing.sectionNonvanishing_pullback f s)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.SectionRestriction

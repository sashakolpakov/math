import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSections
import Mathlib.AlgebraicGeometry.Properties

/-! # Reduced Sections Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ReducedSectionsEq.Construction.ReducedSections

/-! Local equality detection and nonzero sections of line bundles on reduced schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSections

universe u

theorem moduleMap_eq_of_locally {X : Scheme.{u}} {L M : X.Modules} (a b : L ⟶ M)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (Scheme.Modules.pullback U.ι).map a = (Scheme.Modules.pullback U.ι).map b) :
    a = b := by
  have hs (x : X) :
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map a.mapPresheaf =
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map b.mapPresheaf := by
    obtain ⟨U, hx, hU⟩ := h x
    have hr : (Scheme.Modules.restrictFunctor U.ι).map a =
        (Scheme.Modules.restrictFunctor U.ι).map b := by
      apply (cancel_mono ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).hom).mp
      exact ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.naturality a).trans
        ((congrArg (fun z => ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L).hom ≫ z)
          hU).trans ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.naturality b).symm)
    let y : U.toScheme := ⟨x, hx⟩
    let e := Scheme.Modules.restrictStalkNatIso U.ι y
    have ht := congrArg (fun z => ((Scheme.Modules.toPresheaf U.toScheme) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map z) hr
    apply (cancel_epi (e.app L).hom).mp
    exact (e.hom.naturality a).symm.trans
      ((congrArg (fun z => z ≫ (e.app M).hom) ht).trans (e.hom.naturality b))
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  apply TopCat.Presheaf.section_ext (⟨M.presheaf, M.isSheaf⟩ :
    TopCat.Sheaf AddCommGrpCat.{u} X) U
  intro x hx
  change M.presheaf.germ U x hx (a.mapPresheaf.app (.op U) s) =
    M.presheaf.germ U x hx (b.mapPresheaf.app (.op U) s)
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply,
    ← TopCat.Presheaf.stalkFunctor_map_germ_apply, hs x]

theorem section_eq_zero_of_nonvanishing_eq_bot {X : Scheme.{u}} [IsReduced X]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf)
    (hs : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s = ⊥) : s = 0 := by
  apply moduleMap_eq_of_locally
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial x
  refine ⟨U, hx, ?_⟩
  let t : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) := AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s ≫ e.hom
  have ht : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t = ⊥ := by
    rw [AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso, AbelianModuli.HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback, hs]
    rfl
  have hz : AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue U.toScheme t = 0 := by
    apply eq_zero_of_basicOpen_eq_bot
    exact (AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_scalar t).symm.trans ht
  have ht0 : t = 0 := (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv U.toScheme).injective
    (hz.trans (map_zero (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv U.toScheme)).symm)
  rw [Functor.map_zero]
  apply (cancel_epi (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso U.ι).inv).mp
  apply (cancel_mono e.hom).mp
  simpa only [t, AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, comp_zero, zero_comp] using ht0

theorem nonvanishing_eq_bot_iff {X : Scheme.{u}} [IsReduced X]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s = ⊥ ↔ s = 0 := by
  constructor
  · exact section_eq_zero_of_nonvanishing_eq_bot L s
  · rintro rfl
    exact L.sectionNonvanishing_zero

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ReducedSectionsEq.Construction.ReducedSections

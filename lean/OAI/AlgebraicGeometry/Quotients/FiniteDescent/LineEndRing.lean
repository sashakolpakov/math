import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineScalarRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperFunctionsEq

/-! # Line End Ring -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineEndRing.Construction.LineScalars

noncomputable section

/-! The endomorphism ring of a line bundle is the ring of global regular functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing

universe u

variable {X : Scheme.{u}}

theorem scalar_surjective (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : Function.Surjective (ModuleScalarsApp.Construction.ModuleScalars.scalarHom L.sheaf) := by
  intro a
  choose U hx he using L.locallyTrivial
  let e (x : X) : (Scheme.Modules.pullback (U x).ι).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (U x).toScheme :=
    Classical.choice (he x)
  let q (x : X) : Γ(X, U x) :=
    (U x).topIso.hom (LineScalarsEq.Construction.LineScalars.frameValue (e x) ((Scheme.Modules.pullback (U x).ι).map a))
  have hq (i j : X) :
      X.presheaf.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (q i) =
        X.presheaf.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (q j) := by
    let V := U i ⊓ U j
    let eV : (Scheme.Modules.pullback V.ι).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule V.toScheme :=
      L.frameRestrict inf_le_left (e i)
    dsimp only [q]
    rw [LineScalarRestriction.Construction.LineScalars.topIso_homOfLE, LineScalarRestriction.Construction.LineScalars.topIso_homOfLE]
    exact congrArg V.topIso.hom
      ((LineScalarRestriction.Construction.LineScalars.frameValue_homOfLE inf_le_left (e i) eV a).trans
        (LineScalarRestriction.Construction.LineScalars.frameValue_homOfLE inf_le_right (e j) eV a).symm)
  obtain ⟨s, hs, _⟩ := AbelianModuli.HilbertConstruction.Section.Gluing.moduleSection_glue (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U
    (fun x => ⟨x, hx x⟩) q hq
  let r : Γ(X, ⊤) := AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X s
  have hr (x : X) : (U x).ι.appTop r =
      LineScalarsEq.Construction.LineScalars.frameValue (e x) ((Scheme.Modules.pullback (U x).ι).map a) := by
    apply (ConcreteCategory.bijective_of_isIso (U x).topIso.hom).1
    rw [LineScalarRestriction.Construction.LineScalars.topIso_appTop]
    exact (AbelianModuli.HilbertConstruction.RestrictionScalars.structureModuleEndValue_onOpen s (U x)).symm.trans (hs x)
  refine ⟨r, ?_⟩
  change ModuleScalarsApp.Construction.ModuleScalars.scalar L.sheaf r = a
  apply ReducedSectionsEq.Construction.ReducedSections.moduleMap_eq_of_locally
  intro x
  refine ⟨U x, hx x, ?_⟩
  rw [ModuleScalarsApp.Construction.ModuleScalars.pullback_scalar, hr x]
  exact LineScalarsEq.Construction.LineScalars.scalar_eq_of_frame (e x) ((Scheme.Modules.pullback (U x).ι).map a)

/-- Scalar multiplication identifies global functions with all endomorphisms
of the line bundle. -/
def endRingEquiv (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : Γ(X, ⊤) ≃+* End L.sheaf :=
  RingEquiv.ofBijective (ModuleScalarsApp.Construction.ModuleScalars.scalarHom L.sheaf)
    ⟨LineScalarsEq.Construction.LineScalars.scalar_injective L, scalar_surjective L⟩

theorem isIso_of_ne_zero {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom] [ConnectedSpace X.left] [IsReduced X.left]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (a : End L.sheaf) (ha : a ≠ 0) : IsIso a := by
  let r := (endRingEquiv L).symm a
  have hr : r ≠ 0 := by
    intro h
    have he := congrArg (endRingEquiv L) h
    exact ha (by simpa only [r, RingEquiv.apply_symm_apply, map_zero] using he)
  have hu : IsUnit r := (ProperFunctionsEq.Construction.ProperFunctions.section_eq_zero_or_isUnit X r).resolve_left hr
  have haunit : IsUnit a := by
    have h := hu.map (endRingEquiv L).toRingHom
    simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      r, RingEquiv.apply_symm_apply] using h
  exact (isUnit_iff_isIso a).mp haunit

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineEndRing.Construction.LineScalars

import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenFrames

/-! # Restricted Unit Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RestrictedUnitFrame

noncomputable section

/-! A map to the structure sheaf agrees with a restriction frame exactly
when its map on the equivalent over-site agrees with that frame. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (U : X.Opens)

theorem unit_comparison :
    ((Scheme.Modules.overFunctorEquiv U).app (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)).hom ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom =
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom := by
  ext V r
  change (U.ι.appIso V).hom
    (((Scheme.Modules.overFunctorEquiv U).app (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)).hom.val.app (.op V) r) = r
  simp only [Scheme.Modules.overFunctorEquiv, Scheme.Opens.ι_appIso]
  rfl

theorem over_map_comparison {M : X.Modules} (g : M ⟶ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) :
    (Scheme.Modules.overEquiv U).functor.map (g.over U) ≫
        (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom =
      ((Scheme.Modules.overFunctorEquiv U).app M).hom ≫
        (Scheme.Modules.restrictFunctor U.ι).map g ≫ (Scheme.Modules.restrictUnitIso U.ι).hom := by
  rw [← unit_comparison, ← Category.assoc]
  have h := (Scheme.Modules.overFunctorEquiv U).hom.naturality g
  exact (congrArg (fun f => f ≫ (Scheme.Modules.restrictUnitIso U.ι).hom) h).trans
    (Category.assoc _ _ _)

theorem frame_comparison {M : X.Modules}
    (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
    (Scheme.Modules.overEquiv U).functor.map
        (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e).hom ≫
        (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom =
      ((Scheme.Modules.overFunctorEquiv U).app M).hom ≫ e.hom := by
  simp only [AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso,
    Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem restriction_eq_of_over_eq {M : X.Modules} (g : M ⟶ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (h : g.over U = (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e).hom) :
    (Scheme.Modules.restrictFunctor U.ι).map g ≫ (Scheme.Modules.restrictUnitIso U.ι).hom = e.hom := by
  apply (cancel_epi ((Scheme.Modules.overFunctorEquiv U).app M).hom).mp
  rw [← over_map_comparison, h, frame_comparison]

theorem over_eq_of_restriction_eq {M : X.Modules} (g : M ⟶ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme)
    (h : (Scheme.Modules.restrictFunctor U.ι).map g ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom = e.hom) :
    g.over U = (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e).hom := by
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  apply (cancel_mono (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom).mp
  rw [over_map_comparison, h, frame_comparison]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RestrictedUnitFrame

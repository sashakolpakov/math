import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameComparisonTransitions
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FramedLocalHom
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenFrames

/-! # Over Frame Comparisons -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverFrameComparisons

noncomputable section

/-! Comparisons of rank-one frames commute with over-site restriction
and transport faithfully from native open-subscheme frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X : Scheme.{u}} {M N : X.Modules}

theorem linearHomRestrict_frameComparison {U V : X.Opens} (h : V ≤ U)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (f : N.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    SheafCohomology.Projective.LinearHom.linearHomRestrict X.ringCatSheaf M N (homOfLE h).op (e.hom ≫ f.inv) =
      (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e
        (Over.mk (homOfLE h))).hom ≫
      (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf N U f
        (Over.mk (homOfLE h))).inv := by
  simp only [SheafCohomology.Projective.LinearHom.linearHomRestrict, SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rfl

theorem overFrameComparison_map (U : X.Opens)
    (e : M.restrict U.ι ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) (f : N.restrict U.ι ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    (Scheme.Modules.overEquiv U).functor.map
      ((SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e).hom ≫
        (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso N U f).inv) =
      ((Scheme.Modules.overFunctorEquiv U).app M).hom ≫ e.hom ≫ f.inv ≫
        ((Scheme.Modules.overFunctorEquiv U).app N).inv := by
  simp only [Functor.map_comp, SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso,
    Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.preimageIso_inv,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.trans_inv, Category.assoc]
  change ((Scheme.Modules.overFunctorEquiv U).app M).hom ≫
      (e.hom ≫ (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).inv) ≫
      ((U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom ≫ f.inv) ≫
      ((Scheme.Modules.overFunctorEquiv U).app N).inv = _
  have h := (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).inv_hom_id_assoc
    (f.inv ≫ ((Scheme.Modules.overFunctorEquiv U).app N).inv)
  simpa only [Category.assoc] using! congrArg
    (fun q => ((Scheme.Modules.overFunctorEquiv U).app M).hom ≫ e.hom ≫ q) h

theorem overFrameComparison_eq_of_transition (U : X.Opens)
    (e f : M.restrict U.ι ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) (g h : N.restrict U.ι ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (he : FrameTransitionCocycles.frameTransitionValue e f = FrameTransitionCocycles.frameTransitionValue g h) :
    (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e).hom ≫
        (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso N U g).inv =
      (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U f).hom ≫
        (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso N U h).inv := by
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  rw [overFrameComparison_map, overFrameComparison_map]
  simpa only [Category.assoc] using congrArg
    (fun q => ((Scheme.Modules.overFunctorEquiv U).app M).hom ≫ q ≫
      ((Scheme.Modules.overFunctorEquiv U).app N).inv)
    (FrameComparisonTransitions.frameComparison_eq_of_transition e f g h he)

theorem linearHomRestrict_nativeFrameComparison {U V : X.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) (f : N.restrict U.ι ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    SheafCohomology.Projective.LinearHom.linearHomRestrict X.ringCatSheaf M N (homOfLE h).op
      ((SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e).hom ≫
        (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso N U f).inv) =
      (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M V (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h e)).hom ≫
        (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso N V (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h f)).inv := by
  have he := SheafCohomology.Projective.OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization h e
  have hf := SheafCohomology.Projective.OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization h f
  have hc := congrArg₂ (fun
      (a : M.over V ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over V))
      (b : N.over V ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over V)) => a.hom ≫ b.inv) he hf
  exact (linearHomRestrict_frameComparison h
    (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e)
    (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso N U f)).trans hc.symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverFrameComparisons

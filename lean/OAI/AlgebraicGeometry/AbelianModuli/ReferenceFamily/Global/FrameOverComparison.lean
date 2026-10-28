import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReducedFrame
import OAI.RepresentationTheory.Theta.Geometric.Pullback.OpenFrameRestriction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.RestrictionUnit

/-! # Frame Over Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.FrameOverComparison

noncomputable section

section

/-! The actual restriction of a global frame agrees with the native
pullback frame, and remains the same under further open restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} {M : X.Modules} (e : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)

def globalOpenFrame (U : X.Opens) : M.restrict U.ι ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme :=
  (Scheme.Modules.restrictFunctor U.ι).mapIso e ≪≫ Scheme.Modules.restrictUnitIso U.ι

theorem globalOpenFrame_pullback (U : X.Opens) :
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ globalOpenFrame e U =
      RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame U.ι e := by
  apply Iso.ext
  change (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app M ≫
      (Scheme.Modules.restrictFunctor U.ι).map e.hom ≫ (Scheme.Modules.restrictUnitIso U.ι).hom =
    (Scheme.Modules.pullback U.ι).map e.hom ≫ (SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso U.ι).hom
  erw [← Category.assoc, ← (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.naturality e.hom,
    Category.assoc, SheafCohomology.Projective.RestrictionUnit.restrictFunctorIsoPullback_inv_comp_restrictUnitIso]
  rfl

theorem factoredGlobalFrame {Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) :
    RepresentationTheory.Theta.Geometric.FactoredPullbackFrames.factoredPullbackFrame f g (RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame g e) =
      RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame (f ≫ g) e := by
  unfold RepresentationTheory.Theta.Geometric.FactoredPullbackFrames.factoredPullbackFrame
  erw [← RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame_comp f g e]
  exact Iso.symm_self_id_assoc _ _

theorem pullbackGlobalFrame_transport {Y : Scheme.{0}} {f g : Y ⟶ X} (h : f = g) :
    (Scheme.Modules.pullbackCongr h).app M ≪≫ RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame g e =
      RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame f e := by
  cases h
  exact Iso.refl_trans _

theorem globalOpenFrame_restrict {U V : X.Opens} (h : V ≤ U) :
    SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h (globalOpenFrame e U) = globalOpenFrame e V := by
  let a := (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm.app M
  have h₁ := RepresentationTheory.Theta.Geometric.OpenFramesFactored.restrictOpenFrame_as_factored M h (globalOpenFrame e U)
  let b := (Scheme.Modules.pullbackCongr (X.homOfLE_ι h).symm).app M
  have h₂ := congrArg (fun q : (Scheme.Modules.pullback U.ι).obj M ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme =>
    b ≪≫ RepresentationTheory.Theta.Geometric.FactoredPullbackFrames.factoredPullbackFrame (X.homOfLE h) U.ι q) (globalOpenFrame_pullback e U)
  have h₃ := congrArg (fun q => b ≪≫ q) (factoredGlobalFrame e (X.homOfLE h) U.ι)
  have h₄ := pullbackGlobalFrame_transport e (X.homOfLE_ι h).symm
  have h₅ := globalOpenFrame_pullback e V
  apply Iso.ext
  apply (cancel_epi a.hom).mp
  exact congrArg Iso.hom (h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅.symm))))

end

/-! The native over-site frame of a global line-sheaf isomorphism
is its original restricted sheaf map followed by the unit frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem overFrame_precomp {X : Scheme.{0}} {M N : X.Modules} (U : X.Opens)
    (e : M ≅ N) (f : N.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U ((Scheme.Modules.restrictFunctor U.ι).mapIso e ≪≫ f) =
      (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso e ≪≫
        SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso N U f := by
  apply Iso.ext
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  let F := (Scheme.Modules.overEquiv U).functor
  let t := U.sheafOfModulesEquivOverUnit X.ringCatSheaf
  let a := (Scheme.Modules.overFunctorEquiv U).app M ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso e ≪≫ f ≪≫ t.symm
  let b := (Scheme.Modules.overFunctorEquiv U).app N ≪≫ f ≪≫ t.symm
  have ha : F.map (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U
      ((Scheme.Modules.restrictFunctor U.ι).mapIso e ≪≫ f)).hom = a.hom :=
    (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.map_preimage a.hom
  have hb : F.map (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso N U f).hom = b.hom :=
    (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.map_preimage b.hom
  have hn : a.hom = F.map ((SheafOfModules.overFunctor X.ringCatSheaf U).map e.hom) ≫ b.hom :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ f.hom ≫ t.inv)
        ((Scheme.Modules.overFunctorEquiv U).hom.naturality e.hom).symm).trans (Category.assoc _ _ _))
  exact ha.trans (hn.trans ((congrArg
    (fun a => F.map ((SheafOfModules.overFunctor X.ringCatSheaf U).map e.hom) ≫ a) hb).symm.trans
      (F.map_comp _ _).symm))

theorem globalOpenFrame_over {X : Scheme.{0}} {M : X.Modules}
    (e : M ≅ HilbertConstruction.Line.Bundles.structureModule X) (U : X.Opens) :
    SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U (globalOpenFrame e U) =
      (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso e ≪≫
        SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso (HilbertConstruction.Line.Bundles.structureModule X) U (Scheme.Modules.restrictUnitIso U.ι) :=
  overFrame_precomp U e (Scheme.Modules.restrictUnitIso U.ι)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.FrameOverComparison

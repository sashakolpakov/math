import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Local
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleSectionIsomorphisms
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverGenerator
import OAI.RepresentationTheory.Theta.Geometric.FramedUnitGluing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameCoordinates

/-! # Cech Frame -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CechFrame
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open OAI.AlgebraicGeometry.SheafCohomology.Projective.OverGenerator
section

/-! A regular unit cocycle on an actual algebraic open cover
constructs an actual line bundle and its original local frames. -/

variable {X : Scheme.{0}} {I : Type} (U : I → X.Opens) (r : TransitionCocycle.RegularTransitionCoefficients U)
    (hr : TransitionCocycle.RegularTransitionCocycle U r)

theorem regularCechLine_overGenerator_isIso (j : I) :
    IsIso (SheafCohomology.Projective.OverGenerator.overGeneratorHom (Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)) (U j)
      (CechGenerator.regularCechLineGenerator U r hr j)) := by
  apply ModuleSectionIsomorphisms.moduleSheaf_isIso_of_section_bijective
  intro V
  exact Cech.Local.regularCechLineLocalGenerator_bijective U r hr j V.unop.left (leOfHom V.unop.hom)

def regularCechLineFrame (j : I) :
    (Scheme.Modules.pullback (U j).ι).obj (Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)) ≅
      HilbertConstruction.Line.Bundles.structureModule (U j).toScheme := by
  let M := Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)
  let : IsIso (SheafCohomology.Projective.OverGenerator.overGeneratorHom M (U j) (CechGenerator.regularCechLineGenerator U r hr j)) :=
    regularCechLine_overGenerator_isIso U r hr j
  exact ((Scheme.Modules.restrictFunctorIsoPullback (U j).ι).app M).symm ≪≫
    ((Scheme.Modules.overFunctorEquiv (U j)).app M).symm ≪≫
    ((Scheme.Modules.overEquiv (U j)).functor.mapIso
      (asIso (SheafCohomology.Projective.OverGenerator.overGeneratorHom M (U j) (CechGenerator.regularCechLineGenerator U r hr j)))).symm ≪≫
    (U j).sheafOfModulesEquivOverUnit X.ringCatSheaf

def regularCechLineBundle (hU : IsOpenCover U) : HilbertConstruction.Line.Bundles.LineBundle X where
  sheaf := Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)
  locallyTrivial x := by
    obtain ⟨j, hj⟩ := hU.exists_mem x
    exact ⟨U j, hj, ⟨regularCechLineFrame U r hr j⟩⟩

end

/-! The constructed local frames have the prescribed regular transition
functions on every actual overlap. -/

variable {X : Scheme.{0}} {I : Type} (U : I → X.Opens)
    (r : TransitionCocycle.RegularTransitionCoefficients U) (hr : TransitionCocycle.RegularTransitionCocycle U r)

theorem regularCechLineLocalGenerator_transition (i j : I) (W : X.Opens)
    (hi : W ≤ U i) (hj : W ≤ U j) :
    Cech.Local.regularCechLineLocalGenerator U r hr i W hi =
      (TransitionCocycle.regularTransitionOn U r i j W hi hj).val • Cech.Local.regularCechLineLocalGenerator U r hr j W hj := by
  apply Cech.LineSections.cechLineModule_sections_injective U (CechGenerator.regularCechCoefficients U r) W
  rw [Cech.Local.regularCechLineLocalGenerator_inclusion, Cech.Local.regularCechLineLocalGenerator_smul_inclusion]
  have h := Cech.Local.cechCompatible_eq_generator U r W (CechGenerator.regularCechGenerator U r i W hi)
    (CechGenerator.regularCechGenerator_compatible U r hr i W hi) j hj
  rw [Cech.Local.cechZeroValueOn_generator] at h
  exact h

def regularCechOverFrame (j : I) :
    (Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)).over (U j) ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over (U j)) := by
  let : IsIso (SheafCohomology.Projective.OverGenerator.overGeneratorHom (Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)) (U j)
      (CechGenerator.regularCechLineGenerator U r hr j)) := regularCechLine_overGenerator_isIso U r hr j
  exact (asIso (SheafCohomology.Projective.OverGenerator.overGeneratorHom (Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)) (U j)
    (CechGenerator.regularCechLineGenerator U r hr j))).symm

theorem regularCechOverFrame_restrict_inv (j : I) (W : X.Opens) (hj : W ≤ U j) :
    (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf
      (Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)) (U j) (regularCechOverFrame U r hr j)
      (Over.mk (homOfLE hj))).inv =
        SheafCohomology.Projective.OverGenerator.overGeneratorHom (Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)) W
          (Cech.Local.regularCechLineLocalGenerator U r hr j W hj) := by
  let M := Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)
  have h := congrArg Iso.hom ((RepresentationTheory.Theta.Geometric.FramedUnitRestriction.overIsoRestrict_symm
    (M := M) (N := SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) hj (regularCechOverFrame U r hr j)).trans
      (congrArg Iso.symm (RepresentationTheory.Theta.Geometric.FramedUnitRestriction.overIsoRestrict_frame hj (regularCechOverFrame U r hr j))))
  exact h.symm.trans (SheafCohomology.Projective.OverGeneratorRestriction.linearHomRestrict_overGeneratorHom M hj (CechGenerator.regularCechLineGenerator U r hr j))

theorem regularCechOverFrame_transition (i j : I) (W : X.Opens)
    (hi : W ≤ U i) (hj : W ≤ U j) :
    (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf
      (Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)) (U i) (regularCechOverFrame U r hr i)
      (Over.mk (homOfLE hi))).hom =
    (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf
      (Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)) (U j) (regularCechOverFrame U r hr j)
      (Over.mk (homOfLE hj))).hom ≫
        SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W (TransitionCocycle.regularTransitionOn U r j i W hj hi).val := by
  let M := Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)
  let e := SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (U i)
    (regularCechOverFrame U r hr i) (Over.mk (homOfLE hi))
  let g := SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M (U j)
    (regularCechOverFrame U r hr j) (Over.mk (homOfLE hj))
  change e.hom = g.hom ≫ _
  apply (cancel_epi g.inv).mp
  apply (cancel_mono e.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  rw [regularCechOverFrame_restrict_inv, regularCechOverFrame_restrict_inv,
    SheafCohomology.Projective.OverGeneratorRestriction.overUnitScalarEnd_comp_overGeneratorHom, regularCechLineLocalGenerator_transition U r hr j i W hj hi]

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CechFrame

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily

/-! Recover an actual line sheaf from its original local frame cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.SheafCohomology.Projective.OverGenerator

variable {X : Scheme.{0}} {I : Type} {M : X.Modules}

def Regular.CechFrame.lineFrameRegularCoefficients (s : I → LineFrameAtlas.LocalLineFrame M) :
    Regular.TransitionCocycle.RegularTransitionCoefficients (fun i => (s i).domain) :=
  fun i j => (s j).transition (s i) ((s i).domain ⊓ (s j).domain) inf_le_right inf_le_left

theorem Regular.CechFrame.lineFrameRegularCoefficients_on (s : I → LineFrameAtlas.LocalLineFrame M)
    (i j : I) (W : X.Opens) (hi : W ≤ (s i).domain) (hj : W ≤ (s j).domain) :
    Regular.TransitionCocycle.regularTransitionOn (fun i => (s i).domain) (Regular.CechFrame.lineFrameRegularCoefficients s) i j W hi hj =
      (s j).transition (s i) W hj hi :=
  LineFrameAtlas.LocalLineFrame.transition_restrict (s j) (s i) (le_inf hi hj) inf_le_right inf_le_left

theorem Regular.CechFrame.lineFrameRegularCoefficients_cocycle (s : I → LineFrameAtlas.LocalLineFrame M) :
    Regular.TransitionCocycle.RegularTransitionCocycle (fun i => (s i).domain) (Regular.CechFrame.lineFrameRegularCoefficients s) := by
  intro i j k
  rw [Regular.CechFrame.lineFrameRegularCoefficients_on, Regular.CechFrame.lineFrameRegularCoefficients_on, Regular.CechFrame.lineFrameRegularCoefficients_on,
    mul_comm]
  exact LineFrameAtlas.LocalLineFrame.transition_cocycle (s k) (s j) (s i) _ _ _ _

theorem LineFrameAtlas.LocalLineFrame.overFrame_transition (s t : LineFrameAtlas.LocalLineFrame M) (W : X.Opens)
    (hs : W ≤ s.domain) (ht : W ≤ t.domain) :
    (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M s.domain
      (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M s.domain s.frame)
      (Over.mk (homOfLE hs))).hom =
    (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M t.domain
      (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M t.domain t.frame)
      (Over.mk (homOfLE ht))).hom ≫
        SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W (s.transition t W hs ht).val := by
  have h := SheafCohomology.Projective.OverFrameScalarTransfer.overTrivializationOfRestrictIso_hom_eq_comp_scalar M W _ _ _
    (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit_spec M W (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hs s.frame)
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization ht t.frame))
  have he := congrArg Iso.hom (SheafCohomology.Projective.OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization hs s.frame)
  have hg := congrArg Iso.hom (SheafCohomology.Projective.OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization ht t.frame)
  exact he.symm.trans (h.trans (congrArg₂ (· ≫ ·) hg
    (congrArg (fun a : Γ(X, W)ˣ => SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W a.val)
      (LineFrameAtlas.LocalLineFrame.transition_native M s t W hs ht).symm)))

theorem Regular.CechFrame.regularCechLineBundle_iso_of_frames (s : I → LineFrameAtlas.LocalLineFrame M)
    (hU : IsOpenCover (fun i => (s i).domain)) :
    Nonempty ((Regular.CechFrame.regularCechLineBundle (fun i => (s i).domain) (Regular.CechFrame.lineFrameRegularCoefficients s)
      (Regular.CechFrame.lineFrameRegularCoefficients_cocycle s) hU).sheaf ≅ M) := by
  let U := fun i => (s i).domain
  let r := Regular.CechFrame.lineFrameRegularCoefficients s
  let hr := Regular.CechFrame.lineFrameRegularCoefficients_cocycle s
  let a : ∀ i j, Γ(X, U i ⊓ U j) := fun i j => (Regular.TransitionCocycle.regularTransitionOn U r j i _ inf_le_right inf_le_left).val
  obtain ⟨f, _⟩ := RepresentationTheory.Theta.Geometric.FramedUnitGluing.exists_iso_of_framed_units
    (Cech.LineModule.cechLineModule U (Regular.CechGenerator.regularCechCoefficients U r)) M U hU.iSup_eq_top
    (Regular.CechFrame.regularCechOverFrame U r hr)
    (fun i => SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso M (U i) (s i).frame)
    (fun _ => 1) a a
    (fun i j => Regular.CechFrame.regularCechOverFrame_transition U r hr i j _ inf_le_left inf_le_right)
    (fun i j => by
      change _ = _ ≫ SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf _
        (Regular.TransitionCocycle.regularTransitionOn U r j i _ inf_le_right inf_le_left).val
      rw [Regular.CechFrame.lineFrameRegularCoefficients_on]
      exact LineFrameAtlas.LocalLineFrame.overFrame_transition (s i) (s j) _ inf_le_left inf_le_right)
    (fun _ _ => by simp only [RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit, map_one, Units.val_one, mul_one, one_mul])
  exact ⟨f⟩

end AlgebraicGeometry.AbelianModuli.ReferenceFamily

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CechFrame

/-! Native algebraic frames of the constructed cocycle line retain the
specified unit on every overlap. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective.OverGenerator

variable {X : Scheme.{0}} {I : Type} (U : I → X.Opens)
    (r : TransitionCocycle.RegularTransitionCoefficients U) (hr : TransitionCocycle.RegularTransitionCocycle U r)

def regularCechNativeFrame (j : I) : LineFrameAtlas.LocalLineFrame (Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)) :=
  ⟨U j, SheafCohomology.Projective.FrameSections.restrictTrivializationOfOverIso _ (U j) (regularCechOverFrame U r hr j)⟩

theorem regularCechNativeFrame_restrict (j : I) (W : X.Opens) (hj : W ≤ U j) :
    SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hj (regularCechNativeFrame U r hr j).frame =
      SheafCohomology.Projective.FrameSections.restrictTrivializationOfOverIso (Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)) W
        (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf
          (Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)) (U j) (regularCechOverFrame U r hr j)
          (Over.mk (homOfLE hj))) := by
  exact congrArg (fun e => SheafCohomology.Projective.FrameSections.restrictTrivializationOfOverIso _ W
    (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf _ (U j) e (Over.mk (homOfLE hj))))
    (SheafCohomology.Projective.OpenFrames.overTrivializationOfRestrictTrivializationOfOverIso _ (U j) (regularCechOverFrame U r hr j))

theorem regularCechNativeFrame_transition (i j : I) (W : X.Opens)
    (hi : W ≤ U i) (hj : W ≤ U j) :
    (regularCechNativeFrame U r hr i).transition (regularCechNativeFrame U r hr j) W hi hj =
      TransitionCocycle.regularTransitionOn U r j i W hj hi := by
  let M := Cech.LineModule.cechLineModule U (CechGenerator.regularCechCoefficients U r)
  refine (LineFrameAtlas.LocalLineFrame.transition_native M _ _ W hi hj).trans ?_
  apply Eq.symm
  apply RepresentationTheory.Theta.Geometric.FrameTransitionUnitCoherence.frameTransitionUnit_unique
  have h := SheafCohomology.Projective.OverScalarRestriction.restrictTrivializationOfOverIso_hom_eq_comp_scalar M W _ _ _
    (regularCechOverFrame_transition U r hr i j W hi hj)
  have he := congrArg Iso.hom (regularCechNativeFrame_restrict U r hr i W hi)
  have hg := congrArg Iso.hom (regularCechNativeFrame_restrict U r hr j W hj)
  exact he.trans (h.trans (congrArg (· ≫ _) hg.symm))

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CechFrame

end

end OAI

import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareFrame
import OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareComposition
import OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareNaturality

/-! # Global Square Frame -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.GlobalSquareFrame

noncomputable section

section

/-! Coherence of the actual HilbertConstruction frames under composition of section
squares, using the proved native pullback coherence equations. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem structureModulePullbackIso_eq {X Y : Scheme.{0}} (f : X ⟶ Y) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f = SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f := by
  apply Iso.ext
  rfl

theorem lineBundleSquareFrame_eq {X Y B C : Scheme.{0}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (z : B ⟶ X) (frame : (L.pullback z).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B)
    (s : Y ⟶ X) (z' : C ⟶ Y) (r : C ⟶ B) (w : z' ≫ s = r ≫ z) :
    SquareFrame.lineBundleSquareFrame L z frame s z' r w =
      RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame s z' z r w.symm L.sheaf frame := by
  simp only [SquareFrame.lineBundleSquareFrame, RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame, RepresentationTheory.Theta.Geometric.FactoredPullbackFrames.factoredPullbackFrame,
    RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame, structureModulePullbackIso_eq]
  rfl

theorem lineBundleSquareFrame_comp {X Y Z B C D : Scheme.{0}}
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Z) (k : D ⟶ Z) (frame : (L.pullback k).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule D)
    (f : X ⟶ Y) (g : Y ⟶ Z) (i : B ⟶ X) (j : C ⟶ Y) (a : B ⟶ C) (b : C ⟶ D)
    (h₁ : i ≫ f = a ≫ j) (h₂ : j ≫ g = b ≫ k)
    (h₃ : i ≫ (f ≫ g) = (a ≫ b) ≫ k) :
    SquareFrame.lineBundleSquareFrame (L.pullback g) j (SquareFrame.lineBundleSquareFrame L k frame g j b h₂) f i a h₁ =
      (Scheme.Modules.pullback i).mapIso ((Scheme.Modules.pullbackComp f g).app L.sheaf) ≪≫
        SquareFrame.lineBundleSquareFrame L k frame (f ≫ g) i (a ≫ b) h₃ := by
  simp only [lineBundleSquareFrame_eq]
  exact RepresentationTheory.Theta.Geometric.Pullback.SquareComposition.pullbackSquareFrame_comp f g i j k a b h₁.symm h₂.symm h₃.symm L.sheaf frame

theorem lineBundleSquareFrame_naturality {X Y B C : Scheme.{0}}
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (e : L.sheaf ≅ M.sheaf)
    (z : B ⟶ X) (frame : (M.pullback z).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B)
    (s : Y ⟶ X) (z' : C ⟶ Y) (r : C ⟶ B) (w : z' ≫ s = r ≫ z) :
    (Scheme.Modules.pullback z').mapIso ((Scheme.Modules.pullback s).mapIso e) ≪≫
      SquareFrame.lineBundleSquareFrame M z frame s z' r w =
    SquareFrame.lineBundleSquareFrame L z ((Scheme.Modules.pullback z).mapIso e ≪≫ frame) s z' r w := by
  simp only [lineBundleSquareFrame_eq]
  exact RepresentationTheory.Theta.Geometric.Pullback.SquareNaturality.pullbackSquareFrame_naturality s z' z r w.symm e frame

end

/-! The section-square frame of a globally framed line is the
restriction of its actual global frame, with native unit comparisons. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem globalFrame_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g)
    {M : Y.Modules} (e : M ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) :
    (Scheme.Modules.pullbackCongr h).app M ≪≫ RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame g e =
      RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame f e := by
  cases h
  simp only [RepresentationTheory.Theta.Geometric.Pullback.FrameEqualities.pullbackCongr_refl_app, Iso.refl_trans]

theorem factoredGlobalFrame {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (e : M ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Z) :
    RepresentationTheory.Theta.Geometric.FactoredPullbackFrames.factoredPullbackFrame f g (RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame g e) =
      RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame (f ≫ g) e := by
  have h := congrArg (fun d => ((Scheme.Modules.pullbackComp f g).app M).symm ≪≫ d)
    (RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame_comp f g e)
  simpa only [RepresentationTheory.Theta.Geometric.FactoredPullbackFrames.factoredPullbackFrame, Iso.trans_assoc, Iso.symm_self_id_assoc] using h.symm

theorem lineBundleSquareFrame_global {X Y A B : Scheme.{0}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (e : L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (z : A ⟶ X) (f : Y ⟶ X)
    (w : B ⟶ Y) (a : B ⟶ A) (h : w ≫ f = a ≫ z) :
    SquareFrame.lineBundleSquareFrame L z
        ((Scheme.Modules.pullback z).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso z) f w a h =
      (Scheme.Modules.pullback w).mapIso
        ((Scheme.Modules.pullback f).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) ≪≫
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso w := by
  rw [lineBundleSquareFrame_eq]
  simp only [structureModulePullbackIso_eq]
  change RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f w z a h.symm L.sheaf (RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame z e) =
    RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame w (RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame f e)
  unfold RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame
  rw [factoredGlobalFrame, globalFrame_congr h, RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame_comp]

theorem lineBundleSquareFrame_global_of_normalized {X Y A B : Scheme.{0}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (e : L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (z : A ⟶ X)
    (frame : (L.pullback z).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A)
    (hz : (Scheme.Modules.pullback z).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso z = frame)
    (f : Y ⟶ X) (w : B ⟶ Y) (a : B ⟶ A) (h : w ≫ f = a ≫ z) :
    SquareFrame.lineBundleSquareFrame L z frame f w a h =
      (Scheme.Modules.pullback w).mapIso
        ((Scheme.Modules.pullback f).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) ≪≫
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso w := by
  rw [← hz]
  exact lineBundleSquareFrame_global L e z f w a h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.GlobalSquareFrame

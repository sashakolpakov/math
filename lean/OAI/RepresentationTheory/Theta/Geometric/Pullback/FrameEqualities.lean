import OAI.RepresentationTheory.Theta.Geometric.FactoredPullbackFrames

/-! # Frame Equalities -/

namespace OAI.RepresentationTheory.Theta.Geometric.Pullback.FrameEqualities

noncomputable section

/-! Equality transport for the canonical pullback frames and comparisons. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

@[simp]
theorem pullbackCongr_refl_app {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr (rfl : f = f)).app M = Iso.refl ((Scheme.Modules.pullback f).obj M) := rfl

theorem pullbackCongr_trans {X Y : Scheme.{u}} {f g h : X ⟶ Y} (p : f = g) (q : g = h) :
    Scheme.Modules.pullbackCongr p ≪≫ Scheme.Modules.pullbackCongr q =
      Scheme.Modules.pullbackCongr (p.trans q) := by
  cases p
  cases q
  simp [Scheme.Modules.pullbackCongr]

theorem pullbackComp_congr_left {X Y Z : Scheme.{u}} {f f' : X ⟶ Y} (p : f = f')
    (g : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullbackCongr p).app ((Scheme.Modules.pullback g).obj M) ≪≫
      (Scheme.Modules.pullbackComp f' g).app M =
    (Scheme.Modules.pullbackComp f g).app M ≪≫
      (Scheme.Modules.pullbackCongr (congrArg (fun a => a ≫ g) p)).app M := by
  cases p
  simp only [pullbackCongr_refl_app, Iso.refl_trans, Iso.trans_refl]

theorem pullbackComp_congr_right {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g g' : Y ⟶ Z} (p : g = g')
    (M : Z.Modules) :
    (Scheme.Modules.pullback f).mapIso ((Scheme.Modules.pullbackCongr p).app M) ≪≫
      (Scheme.Modules.pullbackComp f g').app M =
    (Scheme.Modules.pullbackComp f g).app M ≪≫
      (Scheme.Modules.pullbackCongr (congrArg (fun a => f ≫ a) p)).app M := by
  cases p
  simp only [pullbackCongr_refl_app, Functor.mapIso_refl, Iso.refl_trans, Iso.trans_refl]

theorem factoredPullbackFrame_congr_left {X Y Z : Scheme.{u}} {f f' : X ⟶ Y} (p : f = f')
    (g : Y ⟶ Z) {M : Z.Modules}
    (e : (Scheme.Modules.pullback g).obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) :
    FactoredPullbackFrames.factoredPullbackFrame f g e =
      (Scheme.Modules.pullbackCongr (congrArg (fun a => a ≫ g) p)).app M ≪≫
        FactoredPullbackFrames.factoredPullbackFrame f' g e := by
  cases p
  simp only [pullbackCongr_refl_app, Iso.refl_trans]

theorem factoredPullbackFrame_congr_right {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    {g g' : Y ⟶ Z} (p : g = g') {M : Z.Modules}
    (e : (Scheme.Modules.pullback g').obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) :
    FactoredPullbackFrames.factoredPullbackFrame f g ((Scheme.Modules.pullbackCongr p).app M ≪≫ e) =
      (Scheme.Modules.pullbackCongr (congrArg (fun a => f ≫ a) p)).app M ≪≫
        FactoredPullbackFrames.factoredPullbackFrame f g' e := by
  cases p
  simp only [pullbackCongr_refl_app, Iso.refl_trans]

end

end OAI.RepresentationTheory.Theta.Geometric.Pullback.FrameEqualities

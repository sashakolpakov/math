import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FrameComparison
import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.SectionIso

/-! # Iso Frames -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IsoFrames.Cycles

noncomputable section

/-! # LineBundleCycles: compatible local frame units induced by actual line-bundle sheaf isomorphisms -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FrameComparison.Cycles.LineBundleConstruction

variable {X : Scheme.{0}} {L M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X} (e : L.sheaf ≅ M.sheaf)

def transportedSectionFrame (x : X) (W : X.Opens) (hW : W ≤ M.trivializingOpen x) :
    Γ(L.sheaf, W) ≃ₗ[Γ(X, W)] Γ(X, W) :=
  (Module.SectionIso.BundleCycles.moduleSectionIso e W).trans (M.sectionFrame x W hW)

theorem transportedSectionFrame_naturality (x : X) {V W : X.Opens}
    (hVW : V ≤ W) (hW : W ≤ M.trivializingOpen x) (m : Γ(L.sheaf, W)) :
    transportedSectionFrame e x V (hVW.trans hW) (L.sheaf.presheaf.map (homOfLE hVW).op m) =
      X.presheaf.map (homOfLE hVW).op (transportedSectionFrame e x W hW m) := by
  change M.sectionFrame x V (hVW.trans hW)
    (Module.SectionIso.BundleCycles.moduleSectionIso e V (L.sheaf.presheaf.map (homOfLE hVW).op m)) = _
  rw [Module.SectionIso.BundleCycles.moduleSectionIso_naturality, M.sectionFrame_naturality]
  rfl

/-- The coordinate, in the target frame, of the image of the source generator. -/
def lineBundleIsoTransition (x y : X) (W : X.Opens)
    (hx : W ≤ L.trivializingOpen x) (hy : W ≤ M.trivializingOpen y) : Γ(X, W)ˣ :=
  FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit (transportedSectionFrame e y W hy) (L.sectionFrame x W hx)

theorem lineBundleIsoTransition_restrict (x y : X) {V W : X.Opens} (hVW : V ≤ W)
    (hx : W ≤ L.trivializingOpen x) (hy : W ≤ M.trivializingOpen y) :
    Units.map (X.presheaf.map (homOfLE hVW).op).hom.toMonoidHom (lineBundleIsoTransition e x y W hx hy) =
      lineBundleIsoTransition e x y V (hVW.trans hx) (hVW.trans hy) :=
  FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit_map (X.presheaf.map (homOfLE hVW).op).hom
    (L.sheaf.presheaf.map (homOfLE hVW).op)
    (transportedSectionFrame e y W hy) (L.sectionFrame x W hx)
    (transportedSectionFrame e y V (hVW.trans hy)) (L.sectionFrame x V (hVW.trans hx))
    (transportedSectionFrame_naturality e y hVW hy) (L.sectionFrame_naturality x hVW hx)

theorem lineBundleIsoTransition_four (x w y z : X) (W : X.Opens)
    (hx : W ≤ L.trivializingOpen x) (hw : W ≤ L.trivializingOpen w)
    (hy : W ≤ M.trivializingOpen y) (hz : W ≤ M.trivializingOpen z) :
    M.ambientTransitionOn y z W hy hz * lineBundleIsoTransition e w z W hw hz =
      lineBundleIsoTransition e x y W hx hy * L.ambientTransitionOn x w W hx hw := by
  have h := FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit_four (transportedSectionFrame e y W hy)
    (transportedSectionFrame e z W hz) (L.sectionFrame w W hw) (L.sectionFrame x W hx)
  rw [transportedSectionFrame, transportedSectionFrame, FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit_precompose] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IsoFrames.Cycles

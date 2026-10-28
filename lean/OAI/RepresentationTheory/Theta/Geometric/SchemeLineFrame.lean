import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import OAI.AlgebraicGeometry.DivisorClass.Chern.FramesFrame

/-! # Scheme Line Frame -/

namespace OAI.RepresentationTheory.Theta.Geometric.SchemeLineFrame

noncomputable section

/-! Actual section frames and transition units for line bundles on
arbitrary schemes, for subsequent continuous pullback to compact spaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.DivisorClass.Chern.FramesFrame.Construction

structure SchemeLineAtlas {X : Scheme} (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) where
  domain : X → X.Opens
  contains : ∀ x, x ∈ domain x
  frame : ∀ x, L.sheaf.restrict (domain x).ι ≅ AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.Construction.structureModule (domain x).toScheme

def schemeLineAtlas {X : Scheme} (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : SchemeLineAtlas L where
  domain x := (L.locallyTrivial x).choose
  contains x := (L.locallyTrivial x).choose_spec.1
  frame x := (Scheme.Modules.restrictFunctorIsoPullback ((L.locallyTrivial x).choose).ι).app L.sheaf ≪≫
    (L.locallyTrivial x).choose_spec.2.some

namespace SchemeLineAtlas

variable {X : Scheme} {L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X} (A : SchemeLineAtlas L)

def sectionFrame (x : X) (W : X.Opens) (h : W ≤ A.domain x) :
    Γ(L.sheaf, W) ≃ₗ[Γ(X, W)] Γ(X, W) :=
  AlgebraicGeometry.DivisorClass.Chern.FramesFrame.Construction.frameOnOpen L.sheaf (A.domain x) (A.frame x) W h

theorem sectionFrame_naturality (x : X) {V W : X.Opens}
    (hVW : V ≤ W) (hW : W ≤ A.domain x) (m : Γ(L.sheaf, W)) :
    A.sectionFrame x V (hVW.trans hW) (L.sheaf.presheaf.map (homOfLE hVW).op m) =
      X.presheaf.map (homOfLE hVW).op (A.sectionFrame x W hW m) :=
  AlgebraicGeometry.DivisorClass.Chern.FramesFrame.Construction.frameOnOpen_naturality L.sheaf (A.domain x) (A.frame x) hVW hW m

def transition (x y : X) (W : X.Opens) (hx : W ≤ A.domain x) (hy : W ≤ A.domain y) :
    Γ(X, W)ˣ :=
  AlgebraicGeometry.DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit (A.sectionFrame x W hx) (A.sectionFrame y W hy)

theorem transition_cocycle (x y z : X) (W : X.Opens)
    (hx : W ≤ A.domain x) (hy : W ≤ A.domain y) (hz : W ≤ A.domain z) :
    A.transition x y W hx hy * A.transition y z W hy hz = A.transition x z W hx hz :=
  AlgebraicGeometry.DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit_cocycle _ _ _

theorem transition_restrict (x y : X) {V W : X.Opens}
    (hVW : V ≤ W) (hx : W ≤ A.domain x) (hy : W ≤ A.domain y) :
    Units.map (X.presheaf.map (homOfLE hVW).op).hom.toMonoidHom (A.transition x y W hx hy) =
      A.transition x y V (hVW.trans hx) (hVW.trans hy) :=
  AlgebraicGeometry.DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit_map (X.presheaf.map (homOfLE hVW).op).hom
    (L.sheaf.presheaf.map (homOfLE hVW).op)
    (A.sectionFrame x W hx) (A.sectionFrame y W hy)
    (A.sectionFrame x V (hVW.trans hx)) (A.sectionFrame y V (hVW.trans hy))
    (A.sectionFrame_naturality x hVW hx) (A.sectionFrame_naturality y hVW hy)

end SchemeLineAtlas

end

end OAI.RepresentationTheory.Theta.Geometric.SchemeLineFrame

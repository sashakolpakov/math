import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Recovery Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Bundle-class recovery composes through an isomorphism in either
orientation, independently of the chosen sheaf isomorphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {X Y Z : Over S}

theorem Line.Bundles.LineBundle.inverseRecovery (e : X ≅ Y) (L : Line.Bundles.LineBundle X.left) (M : Line.Bundles.LineBundle Y.left)
    (h : Line.Bundles.LineBundle.pullbackClass e.hom.left (Line.Bundles.LineBundle.classOf M) = Line.Bundles.LineBundle.classOf L) :
    Line.Bundles.LineBundle.pullbackClass e.inv.left (Line.Bundles.LineBundle.classOf L) = Line.Bundles.LineBundle.classOf M := by
  have q := congrArg (Line.Bundles.LineBundle.pullbackClass e.inv.left) h.symm
  exact q.trans ((Line.Bundles.LineBundle.pullbackIso ((Over.forget S).mapIso e)).left_inv (Line.Bundles.LineBundle.classOf M))

theorem Line.Bundles.LineBundle.recoveryThroughInverse (e : X ≅ Y) (q : Z ≅ Y)
    (L : Line.Bundles.LineBundle X.left) (M : Line.Bundles.LineBundle Y.left) (K : Line.Bundles.LineBundle Z.left)
    (he : Line.Bundles.LineBundle.pullbackClass e.hom.left (Line.Bundles.LineBundle.classOf M) = Line.Bundles.LineBundle.classOf L)
    (hq : Line.Bundles.LineBundle.pullbackClass q.hom.left (Line.Bundles.LineBundle.classOf M) = Line.Bundles.LineBundle.classOf K) :
    Line.Bundles.LineBundle.pullbackClass (e ≪≫ q.symm).hom.left (Line.Bundles.LineBundle.classOf K) = Line.Bundles.LineBundle.classOf L := by
  change Line.Bundles.LineBundle.pullbackClass (e.hom.left ≫ q.inv.left) (Line.Bundles.LineBundle.classOf K) = Line.Bundles.LineBundle.classOf L
  rw [Line.Bundles.LineBundle.pullbackClass_comp, Line.Bundles.LineBundle.inverseRecovery q K M hq]
  exact he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

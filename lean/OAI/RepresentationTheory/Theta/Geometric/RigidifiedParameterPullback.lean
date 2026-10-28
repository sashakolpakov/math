import OAI.RepresentationTheory.Theta.Geometric.RigidifiedPicardDifference

/-! # Rigidified Parameter Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.RigidifiedParameterPullback

noncomputable section

/-! Parameter pullback preserves the original rigidification and the
actual relative Picard value on every test scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite

universe u
variable {K : Type u} [Field K]
    {A B C : Over (Spec (.of K))} [GrpObj A] (D : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A B)

def rigidifiedParameterPullback (f : C ⟶ B) : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A C where
  bundle := D.line f
  axis := D.frame f

theorem rigidifiedParameterPullback_relativeValue (f : C ⟶ B)
    {T : Over (Spec (.of K))} (a : T ⟶ C) :
    (rigidifiedParameterPullback D f).relativeValue a = D.relativeValue (a ≫ f) :=
  congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T)) (D.line_class_pullback a f)

end

end OAI.RepresentationTheory.Theta.Geometric.RigidifiedParameterPullback

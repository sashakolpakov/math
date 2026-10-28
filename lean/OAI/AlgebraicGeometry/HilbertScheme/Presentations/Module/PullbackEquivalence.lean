import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FramePullbackComposition

/-! # Pullback Equivalence -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.PullbackEquivalence

noncomputable section

/-! A scheme isomorphism induces an equivalence of its actual module
sheaf categories, with the usual pullback as forward functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}}

def modulePullbackEquivalence (e : X ≅ Y) : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom) (Scheme.Modules.pullback e.inv)
    ((Scheme.Modules.pullbackId Y).symm ≪≫
      (Scheme.Modules.pullbackCongr e.inv_hom_id).symm ≪≫
        (Scheme.Modules.pullbackComp e.inv e.hom).symm)
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫
      Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫ Scheme.Modules.pullbackId X)

theorem modulePullbackEquivalence_functor (e : X ≅ Y) :
    (modulePullbackEquivalence e).functor = Scheme.Modules.pullback e.hom := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.PullbackEquivalence

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Recovery From Pullback Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveryFromPullbackIso

noncomputable section

/-! An isomorphism with an actual base change gives the corresponding Cartesian recovery morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem schemeRecovery_isPullback_of_overIso
    {S T : Scheme.{u}} {X : Over S} {Y : Over T} (c : S ⟶ T)
    (e : X ≅ (Over.pullback c).obj Y) :
    IsPullback (e.hom.left ≫ pullback.fst Y.hom c) X.hom Y.hom c := by
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  have h : IsPullback e.hom.left X.hom (pullback.snd Y.hom c) (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨e.hom.w.trans (Category.comp_id _).symm⟩
  have H := h.paste_horiz (IsPullback.of_hasPullback Y.hom c)
  exact (congrArg (fun b => IsPullback (e.hom.left ≫ pullback.fst Y.hom c) X.hom Y.hom b)
    (Category.id_comp c)).mp H

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveryFromPullbackIso

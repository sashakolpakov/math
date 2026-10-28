import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.RelativePullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointBaseChange

/-! # Reference Dual Projection -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL

noncomputable section

/-! A genuine PEL comparison with a pulled-back reference family gives
an actual dual projection compatible with every further pullback. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ} {S X T : Scheme.{0}}
    {A : Has.PolarizedActionData E g δ N X} (B : Has.PolarizedActionData E g δ N S)
    (u : X ⟶ S) (a : Iso.PolarizedActionIso (B.pullback u) A)

def Iso.PolarizedActionIso.referenceDualProjection : A.polarized.dual.abelian.scheme.left ⟶ B.polarized.dual.abelian.scheme.left :=
  a.polarized.dual.inv.left ≫ pullback.fst B.polarized.dual.abelian.scheme.hom u

def Iso.PolarizedActionIso.referencePullbackComparison (f : T ⟶ X) :
    Iso.PolarizedActionIso (A.pullback f) (B.pullback (f ≫ u)) :=
  (a.pullback f).symm.trans (Iso.PolarizedActionIso.pullbackComp B u f)

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
theorem Iso.PolarizedActionIso.referencePullbackComparison_dual_fst (f : T ⟶ X) :
    (Iso.PolarizedActionIso.referencePullbackComparison B u a f).polarized.dual.hom.left ≫
        pullback.fst B.polarized.dual.abelian.scheme.hom (f ≫ u) =
      pullback.fst A.polarized.dual.abelian.scheme.hom f ≫ Iso.PolarizedActionIso.referenceDualProjection B u a := by
  change (((Over.pullback f).map a.polarized.dual.inv).left ≫
    (B.polarized.dual.abelian.pullbackCompIso u f).inv.left) ≫
      pullback.fst B.polarized.dual.abelian.scheme.hom (f ≫ u) = _
  rw [Category.assoc, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv_left_fst]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ pullback.fst B.polarized.dual.abelian.scheme.hom u)
      (AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst a.polarized.dual.inv f)).trans (Category.assoc _ _ _))

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
theorem Iso.PolarizedActionIso.pullbackCongr_dual_fst (f h : T ⟶ S) (w : f = h) :
    (Iso.PolarizedActionIso.pullbackCongr B f h w).polarized.dual.hom.left ≫
        pullback.fst B.polarized.dual.abelian.scheme.hom h =
      pullback.fst B.polarized.dual.abelian.scheme.hom f := by
  subst h
  exact Category.id_comp _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL

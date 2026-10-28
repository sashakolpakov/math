import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ProperProductLineUnits

/-! # Translation Ratio -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationRatio

noncomputable section

/-! Two actual subgroup translations differ by a unit on the subgroup parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios OAI.AlgebraicGeometry.Picard.PoincareBundle.ProperProductLineUnits

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H A : Over (Spec (.of k))} [GrpObj A] [IsProper A.hom] [IsIntegral A.left]
  (i : H ⟶ A) (L : Line.Bundles.LineBundle A.left)
  (t s : Line.Fibers.fiber L (snd H A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i))

/-- The unique subgroup unit comparing two global translations. -/
def coefficient : Γ(H.left, ⊤)ˣ := ProperProductLineUnits.baseUnit H A (Line.IsoRatios.ratio (FiberIsomorphismRatios.fiberLine L (snd H A)) t s)

/-- Evaluate the comparison on an arbitrary test-scheme subgroup point. -/
def value {T : Over (Spec (.of k))} (a : T ⟶ H) : Γ(T.left, ⊤)ˣ :=
  Units.map a.left.appTop.hom.toMonoidHom (coefficient i L t s)

theorem point_ratio {T : Over (Spec (.of k))} (x y : T ⟶ A) (a : T ⟶ H) (h : (a ≫ i) * x = y) :
    Line.IsoRatios.ratio (FiberIsomorphismRatios.fiberLine L x) (TranslationFibers.transportIso i L t x y a h) (TranslationFibers.transportIso i L s x y a h) =
      value i L t s a := by
  have hp := FiberIsomorphismRatios.ratio_pullIso L (x := snd H A) (y := NormalizedKernelTranslation.action i) t s (lift a x) x y
    (lift_snd a x) ((TranslationFibers.action_pair i a x).trans h)
  have hf := ProperProductLineUnits.pullback_baseUnit H A (Line.IsoRatios.ratio (FiberIsomorphismRatios.fiberLine L (snd H A)) t s)
  calc
    Line.IsoRatios.ratio (FiberIsomorphismRatios.fiberLine L x) (TranslationFibers.transportIso i L t x y a h) (TranslationFibers.transportIso i L s x y a h) =
        Units.map (lift a x).left.appTop.hom.toMonoidHom (Line.IsoRatios.ratio (FiberIsomorphismRatios.fiberLine L (snd H A)) t s) := hp
    _ = Units.map (lift a x).left.appTop.hom.toMonoidHom
        (Units.map (fst H A).left.appTop.hom.toMonoidHom (coefficient i L t s)) :=
      congrArg (Units.map (lift a x).left.appTop.hom.toMonoidHom) hf.symm
    _ = value i L t s a := by
      apply Units.ext
      change (lift a x ≫ fst H A).left.appTop (coefficient i L t s).val =
        a.left.appTop (coefficient i L t s).val
      rw [lift_fst]

theorem value_natural {T U : Over (Spec (.of k))} (g : U ⟶ T) (a : T ⟶ H) :
    Units.map g.left.appTop.hom.toMonoidHom (value i L t s a) = value i L t s (g ≫ a) := by
  apply Units.ext
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationRatio

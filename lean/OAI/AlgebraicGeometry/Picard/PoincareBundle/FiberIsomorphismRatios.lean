import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

/-! # Fiber Isomorphism Ratios -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios

noncomputable section

/-! Ratios of actual fiber transports commute with native descent pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open Pseudofunctor.LocallyDiscreteOpToCat

variable {S : Scheme.{u}} {A : Over S} (L : Line.Bundles.LineBundle A.left)

theorem fiberLine {T : Over S} (x : T ⟶ A) : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle (Line.Fibers.fiber L x) :=
  Line.Fibers.fiber_isLine L x

/-- Pull back an actual fiber isomorphism through the canonical fiber comparisons. -/
def pullIso {T U : Over S} {x y : T ⟶ A} (e : Line.Fibers.fiber L x ≅ Line.Fibers.fiber L y)
    (g : U ⟶ T) (x' y' : U ⟶ A) (hx : g ≫ x = x') (hy : g ≫ y = y') :
    Line.Fibers.fiber L x' ≅ Line.Fibers.fiber L y' :=
  (Line.Fibers.fiberPullbackIso L g x x' hx).symm ≪≫ (Scheme.Modules.pullback g.left).mapIso e ≪≫
    Line.Fibers.fiberPullbackIso L g y y' hy

theorem pullIso_hom {T U : Over S} {x y : T ⟶ A} (e : Line.Fibers.fiber L x ≅ Line.Fibers.fiber L y)
    (g : U ⟶ T) (x' y' : U ⟶ A) (hx : g ≫ x = x') (hy : g ≫ y = y') :
    (pullIso L e g x' y' hx hy).hom =
      pullHom (F := Geometric.KernelLinearization.overModulePullbacks S) e.hom g x' y' hx hy :=
  (Line.Fibers.pullHom_eq L e.hom g x' y' hx hy).symm

theorem ratio_pullIso {T U : Over S} {x y : T ⟶ A} (e f : Line.Fibers.fiber L x ≅ Line.Fibers.fiber L y)
    (g : U ⟶ T) (x' y' : U ⟶ A) (hx : g ≫ x = x') (hy : g ≫ y = y') :
    Line.IsoRatios.ratio (fiberLine L x') (pullIso L e g x' y' hx hy) (pullIso L f g x' y' hx hy) =
      Units.map g.left.appTop.hom (Line.IsoRatios.ratio (fiberLine L x) e f) := by
  rw [pullIso, pullIso, ← Iso.trans_assoc, ← Iso.trans_assoc, Line.IsoRatios.ratio_postcomp]
  rw [Line.IsoRatios.ratio_precomp (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_pullback g.left (Line.Fibers.fiber L x) (fiberLine L x))
    (fiberLine L x') (Line.Fibers.fiberPullbackIso L g x x' hx).symm]
  exact Line.IsoRatios.ratio_pullback (fiberLine L x) g.left e f

/-- Equal native pullback maps have the pulled-back regular ratio. -/
theorem ratio_natural {T U : Over S} {x y : T ⟶ A} (e f : Line.Fibers.fiber L x ≅ Line.Fibers.fiber L y)
    (g : U ⟶ T) (x' y' : U ⟶ A) (hx : g ≫ x = x') (hy : g ≫ y = y')
    (e' f' : Line.Fibers.fiber L x' ≅ Line.Fibers.fiber L y')
    (he : pullHom (F := Geometric.KernelLinearization.overModulePullbacks S) e.hom g x' y' hx hy = e'.hom)
    (hf : pullHom (F := Geometric.KernelLinearization.overModulePullbacks S) f.hom g x' y' hx hy = f'.hom) :
    Line.IsoRatios.ratio (fiberLine L x') e' f' = Units.map g.left.appTop.hom (Line.IsoRatios.ratio (fiberLine L x) e f) := by
  have he' : pullIso L e g x' y' hx hy = e' := Iso.ext ((pullIso_hom L e g x' y' hx hy).trans he)
  have hf' : pullIso L f g x' y' hx hy = f' := Iso.ext ((pullIso_hom L f g x' y' hx hy).trans hf)
  exact (congrArg₂ (Line.IsoRatios.ratio (fiberLine L x')) he' hf').symm.trans
    (ratio_pullIso L e f g x' y' hx hy)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios

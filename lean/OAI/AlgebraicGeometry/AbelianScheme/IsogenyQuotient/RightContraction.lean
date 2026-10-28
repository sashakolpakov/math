import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BilinearFlip
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ActionLaws

/-! # Right Contraction -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RightContraction.Construction

noncomputable section

/-! Inserting the right input into an actual bilinear line map,
with its section formula and geometric pullback identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

universe u

variable {X : Scheme.{u}} {M N P : X.Modules}

def lineContractRight (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N) : M ⟶ P :=
  Picard.PoincareBundle.Bilinear.Contraction.contractLeft (BilinearFlip.Construction.flipLineBilinear b) s

theorem lineContractRight_app (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N)
    (U : X.Opens) (m : Γ(M, U)) :
    (lineContractRight b s).app U m = b.app U m (s.app U (1 : Γ(X, U))) :=
  Picard.PoincareBundle.Bilinear.Contraction.contractLeft_app (BilinearFlip.Construction.flipLineBilinear b) s U m

theorem lineContractRight_unit (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N M) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N)
    (h : ∀ (U : X.Opens) (m : Γ(M, U)), b.app U m (s.app U (1 : Γ(X, U))) = m) :
    lineContractRight b s = 𝟙 M :=
  Picard.PoincareBundle.Bilinear.ActionLaws.contraction_unit (BilinearFlip.Construction.flipLineBilinear b) s h

theorem lineContractRight_pullback {S : Scheme.{u}} {E T U : Over S}
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left) (r : U ⟶ T)
    (x a y : T ⟶ E) (x' a' y' : U ⟶ E)
    (hx : r ≫ x = x') (ha : r ≫ a = a') (hy : r ≫ y = y')
    (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L a) (Picard.PoincareBundle.Line.Fibers.fiber L y))
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ⟶ Picard.PoincareBundle.Line.Fibers.fiber L a) :
    lineContractRight (Picard.PoincareBundle.Line.Fibers.pullBilinear L r x a y x' a' y' hx ha hy b) (Picard.PoincareBundle.Line.Fibers.pullSection L r a a' ha s) =
      (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r x x' hx).inv ≫
        (Scheme.Modules.pullback r.left).map (lineContractRight b s) ≫
          (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r y y' hy).hom := by
  unfold lineContractRight
  rw [BilinearFlip.Construction.flipLineBilinear_pullBilinear]
  exact Picard.PoincareBundle.Bilinear.Transport.contractLeft_pullback_transport r.left
    (Picard.PoincareBundle.Line.Fibers.fiber_isLine L a) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x) (BilinearFlip.Construction.flipLineBilinear b)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r a a' ha) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r x x' hx) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r y y' hy) s

theorem contractedRightUnit_pullback {S : Scheme.{u}} {E T U : Over S}
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left) (r : U ⟶ T)
    (x a : T ⟶ E) (x' a' : U ⟶ E) (hx : r ≫ x = x') (ha : r ≫ a = a')
    (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L a) (Picard.PoincareBundle.Line.Fibers.fiber L x))
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ⟶ Picard.PoincareBundle.Line.Fibers.fiber L a) (hb : lineContractRight b s = 𝟙 (Picard.PoincareBundle.Line.Fibers.fiber L x)) :
    lineContractRight (Picard.PoincareBundle.Line.Fibers.pullBilinear L r x a x x' a' x' hx ha hx b) (Picard.PoincareBundle.Line.Fibers.pullSection L r a a' ha s) =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber L x') := by
  rw [lineContractRight_pullback, hb, (Scheme.Modules.pullback r.left).map_id,
    Category.id_comp, Iso.inv_hom_id]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RightContraction.Construction

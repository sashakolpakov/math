import OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedProductPresentation

/-! # Presented Framed Product Naturality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PresentedFramedProductNaturality

noncomputable section

/-! A subgroup product presented on individual line fibers is the directly evaluated inducing product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedProductPresentation

variable {S : Scheme.{u}} {A : Over S} [GrpObj A]
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])

/-- Every coordinate presentation restricts to the presentation made directly on the test scheme. -/
theorem restriction {K T : Over S} (p : K ⟶ A ⊗ A)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule K.left ≅ Line.Fibers.fiber (Line.Comparison.Bundle.fromShared Q) p)
    (xK yK zK : K ⟶ A) (hpx : p ≫ fst A A = xK) (hpy : p ≫ snd A A = yK) (hpz : p ≫ μ[A] = zK)
    (q : T ⟶ K) (x y z : T ⟶ A) (hx : q ≫ xK = x) (hy : q ≫ yK = y) (hz : q ≫ zK = z)
    (hpx' : (q ≫ p) ≫ fst A A = x) (hpy' : (q ≫ p) ≫ snd A A = y) (hpz' : (q ≫ p) ≫ μ[A] = z) :
    Bilinear.FiberPresentation.atPointIso L xK yK zK
        (FramedProductPresentation.presentation Q L e p s xK yK zK hpx hpy hpz) q x y z hx hy hz =
      FramedProductPresentation.presentation Q L e (q ≫ p)
        (GlobalPullbackFrame.atPoint p (Line.Comparison.Bundle.fromShared Q) s q (q ≫ p) rfl)
        x y z hpx' hpy' hpz' := by
  let a := Tensor.FiberComposition.comparison L (fst A A) (snd A A) p xK yK hpx hpy
  let b := Line.Fibers.fiberPullbackIso L p μ[A] zK hpz
  let a' := Tensor.FiberComposition.comparison L (fst A A) (snd A A) (q ≫ p) x y hpx' hpy'
  let b' := Line.Fibers.fiberPullbackIso L (q ≫ p) μ[A] z hpz'
  let m := Tensor.FiberComposition.comparison L xK yK q x y hx hy
  let n := Line.Fibers.fiberPullbackIso L q zK z hz
  let cr := (Scheme.Modules.pullbackComp q.left p.left).app (InducingFormulaSymmetry.factorLine A L).sheaf
  let cp := (Scheme.Modules.pullbackComp q.left p.left).app (InducingFormulaSymmetry.targetLine A L).sheaf
  have ha : (Scheme.Modules.pullback q.left).mapIso a ≪≫ m = cr ≪≫ a' :=
    Tensor.FiberComposition.composition L (fst A A) (snd A A) p q xK yK hpx hpy x y hx hy hpx' hpy'
  have hb : (Scheme.Modules.pullback q.left).mapIso b ≪≫ n = cp ≪≫ b' :=
    FiberPullbackComposition.fiberIso_comp_exact L p q μ[A] zK z hpz hz hpz'
  exact PresentedIsoRestriction.restrict (Scheme.Modules.pullback q.left) a b (FramedProductPresentation.mapIso Q L e p s)
    a' b' (FramedProductPresentation.mapIso Q L e (q ≫ p) (GlobalPullbackFrame.atPoint p (Line.Comparison.Bundle.fromShared Q) s q (q ≫ p) rfl))
    cr cp m n ha hb (FramedProductPresentation.mapIso_restriction Q L e p s q)

/-- The same restriction formula permits any specified equal composite point. -/
theorem restriction_to {K T : Over S} (p : K ⟶ A ⊗ A)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule K.left ≅ Line.Fibers.fiber (Line.Comparison.Bundle.fromShared Q) p)
    (xK yK zK : K ⟶ A) (hpx : p ≫ fst A A = xK) (hpy : p ≫ snd A A = yK) (hpz : p ≫ μ[A] = zK)
    (q : T ⟶ K) (v : T ⟶ A ⊗ A) (hv : q ≫ p = v)
    (x y z : T ⟶ A) (hx : q ≫ xK = x) (hy : q ≫ yK = y) (hz : q ≫ zK = z)
    (hpx' : v ≫ fst A A = x) (hpy' : v ≫ snd A A = y) (hpz' : v ≫ μ[A] = z) :
    Bilinear.FiberPresentation.atPointIso L xK yK zK
        (FramedProductPresentation.presentation Q L e p s xK yK zK hpx hpy hpz) q x y z hx hy hz =
      FramedProductPresentation.presentation Q L e v (GlobalPullbackFrame.atPoint p (Line.Comparison.Bundle.fromShared Q) s q v hv)
        x y z hpx' hpy' hpz' := by
  subst v
  exact restriction Q L e p s xK yK zK hpx hpy hpz q x y z hx hy hz hpx' hpy' hpz'

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PresentedFramedProductNaturality

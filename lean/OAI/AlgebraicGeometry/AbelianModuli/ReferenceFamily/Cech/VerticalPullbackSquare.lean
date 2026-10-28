import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechPullbackTotal
import OAI.AlgebraicGeometry.DivisorClass.Chern.FlasqueCechD

/-! # Vertical Pullback Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.VerticalPullbackSquare

noncomputable section

/-! A square of original augmentations gives the same square on the
actual vertical Čech edges, before choosing any resolutions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf
open OAI.AlgebraicGeometry.DivisorClass.Chern.FlasqueCechD OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechPullbackTotal

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {I : Type} (U : I → Opens Y)
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} Y) ℕ}
    {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ}
    (β : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).obj L)
    {F : TopCat.Sheaf AddCommGrpCat.{0} Y} {G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (a : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj G)
    (u : F ⟶ K.X 0) (hu : u ≫ K.d 0 1 = 0)
    (v : G ⟶ L.X 0) (hv : v ≫ L.d 0 1 = 0)

theorem cechVerticalPullbackSquare
    (h : u ≫ β.f 0 = a ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map v) :
    DivisorClass.Chern.FlasqueCechD.abelianCechVerticalEdge U u hu ≫ Comparison.Betti.Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap f U β =
      Comparison.Betti.Cech.PullbackGlobalIsomorphism.additiveCechPullbackMap f U F G a.hom ≫
        DivisorClass.Chern.FlasqueCechD.abelianCechVerticalEdge (fun i => (Opens.map f).obj (U i)) v hv := by
  have hs := Comparison.Betti.Cech.PullbackNaturality.additiveCechPullbackMap_square f U u v a.hom (β.f 0).hom (congrArg (fun z => z.hom) h)
  apply HomologicalComplex.Hom.ext
  funext n
  let B := SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U K
  let C := SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex (fun i => (Opens.map f).obj (U i)) L
  let φ : B ⟶ C := Comparison.Betti.Sheaf.CechPullbackTotal.sheafCechPullbackBicomplexMap f U β
  have hc : ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map u).f n ≫ (φ.f 0).f n =
      (Comparison.Betti.Cech.PullbackGlobalIsomorphism.additiveCechPullbackMap f U F G a.hom).f n ≫
        ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor (fun i => (Opens.map f).obj (U i))).map v).f n :=
    congrArg (fun z => z.f n) hs
  let m := ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map u).f n
  let p := (Comparison.Betti.Cech.PullbackGlobalIsomorphism.additiveCechPullbackMap f U F G a.hom).f n
  let r := ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor (fun i => (Opens.map f).obj (U i))).map v).f n
  let T := (HomologicalComplex₂.total.map φ (.up ℕ)).f n
  have hm : (m ≫ B.ιTotal (.up ℕ) 0 n n (Nat.zero_add n)) ≫ T =
      p ≫ (r ≫ C.ιTotal (.up ℕ) 0 n n (Nat.zero_add n)) :=
    (Category.assoc _ _ _).trans
      ((congrArg (m ≫ ·) (HomologicalComplex₂.ιTotal_map B C φ (.up ℕ) 0 n n (Nat.zero_add n))).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ C.ιTotal (.up ℕ) 0 n n (Nat.zero_add n)) hc).trans (Category.assoc _ _ _))))
  have hl := congrArg (· ≫ T) (DivisorClass.Chern.FlasqueCechD.abelianCechVerticalEdge_f U u hu n)
  have hr := congrArg (p ≫ ·) (DivisorClass.Chern.FlasqueCechD.abelianCechVerticalEdge_f (fun i => (Opens.map f).obj (U i)) v hv n)
  exact hl.trans (hm.trans hr.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.VerticalPullbackSquare

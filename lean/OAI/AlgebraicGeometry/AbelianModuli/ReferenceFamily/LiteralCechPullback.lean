import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CechClasses
import OAI.AlgebraicGeometry.Comparison.Betti.Cech.PushforwardCoordinates

/-! # Literal Cech Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LiteralCechPullback

noncomputable section

/-! Pullback on literal-intersection additive Čech cochains is the
original section morphism followed only by the equality of preimage opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CechClasses

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {I : Type} (U : I → Opens Y)
    (F : Y.Presheaf AddCommGrpCat.{0}) (G : X.Presheaf AddCommGrpCat.{0})

def literalCechPreimageIso {n : ℕ} (t : Fin (n + 1) → I) :
    G.obj (op ((Opens.map f).obj (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U t))) ≅
      G.obj (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun i => (Opens.map f).obj (U i)) t)) :=
  G.mapIso (eqToIso (congrArg op (Comparison.Betti.Cech.PushforwardCoordinates.cechIntersection_preimage f U t)))

variable (a : F ⟶ (Opens.map f).op ⋙ G)

def literalCechPullback (n : ℕ) (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F U n) :
    DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain G (fun i => (Opens.map f).obj (U i)) n :=
  fun t => (literalCechPreimageIso f U G t).hom (a.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U t)) (k t))

theorem literalCechPullback_restriction {n m : ℕ} (t : Fin (n + 1) → I)
    (r : Fin (m + 1) → Fin (n + 1)) :
    F.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U t r)).op ≫
        a.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U t)) ≫ (literalCechPreimageIso f U G t).hom =
      a.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (t ∘ r))) ≫ (literalCechPreimageIso f U G (t ∘ r)).hom ≫
        G.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp (fun i => (Opens.map f).obj (U i)) t r)).op := by
  let j := (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U t r)).op
  have hn := a.naturality j
  have hG : ((Opens.map f).op ⋙ G).map j ≫ (literalCechPreimageIso f U G t).hom =
      (literalCechPreimageIso f U G (t ∘ r)).hom ≫
        G.map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp (fun i => (Opens.map f).obj (U i)) t r)).op := by
    change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
    exact (G.map_comp _ _).symm.trans
      ((congrArg G.map (Subsingleton.elim _ _)).trans (G.map_comp _ _))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (literalCechPreimageIso f U G t).hom) hn).trans
    ((Category.assoc _ _ _).trans (congrArg (a.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (t ∘ r))) ≫ ·) hG)))

theorem literalCechPullback_delta (n : ℕ) (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F U n) :
    literalCechPullback f U F G a (n + 1) (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n k) =
      DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta G (fun i => (Opens.map f).obj (U i)) n (literalCechPullback f U F G a n k) := by
  funext t
  dsimp only [literalCechPullback, DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul, map_zsmul]
  congr 1
  exact ConcreteCategory.congr_hom (literalCechPullback_restriction f U F G a t j.succAbove)
    (k (t ∘ j.succAbove))

theorem literalCechPullback_closed (n : ℕ) (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F U n)
    (hk : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F U n k = 0) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta G (fun i => (Opens.map f).obj (U i)) n (literalCechPullback f U F G a n k) = 0 := by
  rw [← literalCechPullback_delta, hk]
  funext t
  change (literalCechPreimageIso f U G t).hom (a.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U t)) 0) = 0
  rw [map_zero, map_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LiteralCechPullback

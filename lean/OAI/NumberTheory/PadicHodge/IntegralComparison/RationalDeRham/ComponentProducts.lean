import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.TotalComponents

/-! # Component Products -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.ComponentProducts.CechCup

noncomputable section

/-! Product rules in each bidegree after inclusion into the actual
total complex. Degree casts are eliminated by the same inclusion maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Simplicial

universe u

variable (R : Type u) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R)))
  (N : SimplicialObject (FormalCoproduct.{u} X.left.Opens))

theorem component_deRhamDifferential_cup (p q a b k : ℕ) (hk : p + q + 1 + (a + b) = k)
    (x : (CechCup.cochains R X N p).obj ⦋a⦌) (y : (CechCup.cochains R X N q).obj ⦋b⦌) :
    TotalComponents.CechCup.component R X N (p + q + 1) (a + b) k hk
        ((CechDifferential.Cup.deRhamDifferential R X N (p + q)).app ⦋a + b⦌ (CechCup.cup R X N p q a b x y)) =
      TotalComponents.CechCup.component R X N ((p + 1) + q) (a + b) k (by omega)
        (CechCup.cup R X N (p + 1) q a b ((CechDifferential.Cup.deRhamDifferential R X N p).app ⦋a⦌ x) y) +
      (-1 : ℤ) ^ p • TotalComponents.CechCup.component R X N (p + (q + 1)) (a + b) k (by omega)
        (CechCup.cup R X N p (q + 1) a b x ((CechDifferential.Cup.deRhamDifferential R X N q).app ⦋b⦌ y)) := by
  rw [CechDifferential.Cup.deRhamDifferential_cup]
  erw [map_add, map_zsmul, TotalComponents.CechCup.component_formDegreeCast, TotalComponents.CechCup.component_formDegreeCast]
  all_goals omega

theorem component_cechDifferential_cup (p q a b k : ℕ) (hk : (p + q) + (a + b + 1) = k)
    (x : (CechCup.cochains R X N p).obj ⦋a⦌) (y : (CechCup.cochains R X N q).obj ⦋b⦌) :
    TotalComponents.CechCup.component R X N (p + q) (a + b + 1) k hk
        (Cosimplicial.BilinearCup.differential (CechCup.cochains R X N (p + q)) (a + b)
          (CechCup.cup R X N p q a b x y)) =
      TotalComponents.CechCup.component R X N (p + q) ((a + 1) + b) k (by omega)
        (CechCup.cup R X N p q (a + 1) b
          (Cosimplicial.BilinearCup.differential (CechCup.cochains R X N p) a x) y) +
      (-1 : ℤ) ^ a • TotalComponents.CechCup.component R X N (p + q) (a + (b + 1)) k (by omega)
        (CechCup.cup R X N p q a (b + 1) x
          (Cosimplicial.BilinearCup.differential (CechCup.cochains R X N q) b y)) := by
  have hc : Cosimplicial.BilinearCup.differential (CechCup.cochains R X N (p + q)) (a + b)
      (CechCup.cup R X N p q a b x y) =
        Cosimplicial.BilinearDegrees.Cup.degreeCast (CechCup.cochains R X N (p + q))
          (by omega : (a + 1) + b = a + b + 1)
          (CechCup.cup R X N p q (a + 1) b
            (Cosimplicial.BilinearCup.differential (CechCup.cochains R X N p) a x) y) +
        (-1 : ℤ) ^ a • Cosimplicial.BilinearDegrees.Cup.degreeCast (CechCup.cochains R X N (p + q))
          (by omega : a + (b + 1) = a + b + 1)
          (CechCup.cup R X N p q a (b + 1) x
            (Cosimplicial.BilinearCup.differential (CechCup.cochains R X N q) b y)) :=
    Cosimplicial.BilinearDegrees.Cup.differential_cup_cast _ _ _ (CechCup.pairing R X N p q)
      (CechCup.pairing_natural R X N p q) a b x y
  rw [hc]
  erw [map_add, map_zsmul, TotalComponents.CechCup.component_cechDegreeCast, TotalComponents.CechCup.component_cechDegreeCast]
  all_goals omega

theorem differential_component_cup (p q a b k : ℕ) (hk : (p + q) + (a + b) = k)
    (x : (CechCup.cochains R X N p).obj ⦋a⦌) (y : (CechCup.cochains R X N q).obj ⦋b⦌) :
    (TotalCup.Cech.total R X N).d k (k + 1)
        (TotalComponents.CechCup.component R X N (p + q) (a + b) k hk (CechCup.cup R X N p q a b x y)) =
      (TotalComponents.CechCup.component R X N ((p + 1) + q) (a + b) (k + 1) (by omega)
          (CechCup.cup R X N (p + 1) q a b ((CechDifferential.Cup.deRhamDifferential R X N p).app ⦋a⦌ x) y) +
        (-1 : ℤ) ^ p • TotalComponents.CechCup.component R X N (p + (q + 1)) (a + b) (k + 1) (by omega)
          (CechCup.cup R X N p (q + 1) a b x ((CechDifferential.Cup.deRhamDifferential R X N q).app ⦋b⦌ y))) +
      (-1 : ℤ) ^ (p + q) •
        (TotalComponents.CechCup.component R X N (p + q) ((a + 1) + b) (k + 1) (by omega)
            (CechCup.cup R X N p q (a + 1) b
              (Cosimplicial.BilinearCup.differential (CechCup.cochains R X N p) a x) y) +
          (-1 : ℤ) ^ a • TotalComponents.CechCup.component R X N (p + q) (a + (b + 1)) (k + 1) (by omega)
            (CechCup.cup R X N p q a (b + 1) x
              (Cosimplicial.BilinearCup.differential (CechCup.cochains R X N q) b y))) := by
  rw [TotalComponents.CechCup.differential_component, component_deRhamDifferential_cup, component_cechDifferential_cup]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.ComponentProducts.CechCup

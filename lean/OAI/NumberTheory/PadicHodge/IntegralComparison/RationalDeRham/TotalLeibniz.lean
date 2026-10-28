import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.ComponentProducts
import OAI.NumberTheory.PadicHodge.IntegralComparison.TotalProductSigns

/-! # Total Leibniz -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.TotalLeibniz.CechCup

noncomputable section

/-! The graded Leibniz rule for the actual total Čech–de Rham product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Simplicial

universe u

variable (R : Type u) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R)))
  (N : SimplicialObject (FormalCoproduct.{u} X.left.Opens))

theorem cupInto_differential_left_component (n m p a q b : ℕ)
    (hpa : p + a = n) (hqb : q + b = m)
    (x : (CechCup.cochains R X N p).obj ⦋a⦌) (y : (CechCup.cochains R X N q).obj ⦋b⦌) :
    TotalComponents.CechCup.cupInto R X N (n + 1) m (n + m + 1) (by omega)
        ((TotalCup.Cech.total R X N).d n (n + 1) (TotalComponents.CechCup.component R X N p a n hpa x)) (TotalComponents.CechCup.component R X N q b m hqb y) =
      (-1 : ℤ) ^ (a * q) • TotalComponents.CechCup.component R X N ((p + 1) + q) (a + b) (n + m + 1) (by omega)
        (CechCup.cup R X N (p + 1) q a b ((CechDifferential.Cup.deRhamDifferential R X N p).app ⦋a⦌ x) y) +
      (-1 : ℤ) ^ p • ((-1 : ℤ) ^ ((a + 1) * q) •
        TotalComponents.CechCup.component R X N (p + q) ((a + 1) + b) (n + m + 1) (by omega)
          (CechCup.cup R X N p q (a + 1) b
            (Cosimplicial.BilinearCup.differential (CechCup.cochains R X N p) a x) y)) := by
  let B := (TotalComponents.CechCup.cupInto R X N (n + 1) m (n + m + 1) (by omega)).flip
    (TotalComponents.CechCup.component R X N q b m hqb y)
  let u := TotalComponents.CechCup.component R X N (p + 1) a (n + 1) (by omega) ((CechDifferential.Cup.deRhamDifferential R X N p).app ⦋a⦌ x)
  let v := TotalComponents.CechCup.component R X N p (a + 1) (n + 1) (by omega)
    (Cosimplicial.BilinearCup.differential (CechCup.cochains R X N p) a x)
  have hs : B (u + (-1 : ℤ) ^ p • v) = B u + (-1 : ℤ) ^ p • B v :=
    (B.map_add u _).trans (congrArg (B u + ·) (map_zsmul B ((-1 : ℤ) ^ p) v))
  exact (congrArg B (TotalComponents.CechCup.differential_component R X N p a n hpa x)).trans
    (hs.trans (congrArg₂ (fun z w => z + (-1 : ℤ) ^ p • w)
      (TotalComponents.CechCup.cupInto_component R X N (n + 1) m (n + m + 1) (p + 1) a q b (by omega) (by omega) hqb
        ((CechDifferential.Cup.deRhamDifferential R X N p).app ⦋a⦌ x) y)
      (TotalComponents.CechCup.cupInto_component R X N (n + 1) m (n + m + 1) p (a + 1) q b (by omega) (by omega) hqb
        (Cosimplicial.BilinearCup.differential (CechCup.cochains R X N p) a x) y)))

theorem cupInto_differential_right_component (n m p a q b : ℕ)
    (hpa : p + a = n) (hqb : q + b = m)
    (x : (CechCup.cochains R X N p).obj ⦋a⦌) (y : (CechCup.cochains R X N q).obj ⦋b⦌) :
    TotalComponents.CechCup.cupInto R X N n (m + 1) (n + m + 1) (by omega)
        (TotalComponents.CechCup.component R X N p a n hpa x) ((TotalCup.Cech.total R X N).d m (m + 1) (TotalComponents.CechCup.component R X N q b m hqb y)) =
      (-1 : ℤ) ^ (a * (q + 1)) • TotalComponents.CechCup.component R X N (p + (q + 1)) (a + b) (n + m + 1) (by omega)
        (CechCup.cup R X N p (q + 1) a b x ((CechDifferential.Cup.deRhamDifferential R X N q).app ⦋b⦌ y)) +
      (-1 : ℤ) ^ q • ((-1 : ℤ) ^ (a * q) •
        TotalComponents.CechCup.component R X N (p + q) (a + (b + 1)) (n + m + 1) (by omega)
          (CechCup.cup R X N p q a (b + 1) x
            (Cosimplicial.BilinearCup.differential (CechCup.cochains R X N q) b y))) := by
  let B := TotalComponents.CechCup.cupInto R X N n (m + 1) (n + m + 1) (by omega) (TotalComponents.CechCup.component R X N p a n hpa x)
  let u := TotalComponents.CechCup.component R X N (q + 1) b (m + 1) (by omega) ((CechDifferential.Cup.deRhamDifferential R X N q).app ⦋b⦌ y)
  let v := TotalComponents.CechCup.component R X N q (b + 1) (m + 1) (by omega)
    (Cosimplicial.BilinearCup.differential (CechCup.cochains R X N q) b y)
  have hs : B (u + (-1 : ℤ) ^ q • v) = B u + (-1 : ℤ) ^ q • B v :=
    (B.map_add u _).trans (congrArg (B u + ·) (map_zsmul B ((-1 : ℤ) ^ q) v))
  exact (congrArg B (TotalComponents.CechCup.differential_component R X N q b m hqb y)).trans
    (hs.trans (congrArg₂ (fun z w => z + (-1 : ℤ) ^ q • w)
      (TotalComponents.CechCup.cupInto_component R X N n (m + 1) (n + m + 1) p a (q + 1) b (by omega) hpa (by omega)
        x ((CechDifferential.Cup.deRhamDifferential R X N q).app ⦋b⦌ y))
      (TotalComponents.CechCup.cupInto_component R X N n (m + 1) (n + m + 1) p a q (b + 1) (by omega) hpa (by omega)
        x (Cosimplicial.BilinearCup.differential (CechCup.cochains R X N q) b y))))

theorem differential_totalCup_components (n m p a q b : ℕ)
    (hpa : p + a = n) (hqb : q + b = m)
    (x : (CechCup.cochains R X N p).obj ⦋a⦌) (y : (CechCup.cochains R X N q).obj ⦋b⦌) :
    (TotalCup.Cech.total R X N).d (n + m) (n + m + 1)
        (TotalCup.Cech.totalCup R X N n m (TotalComponents.CechCup.component R X N p a n hpa x) (TotalComponents.CechCup.component R X N q b m hqb y)) =
      TotalComponents.CechCup.cupInto R X N (n + 1) m (n + m + 1) (by omega)
        ((TotalCup.Cech.total R X N).d n (n + 1) (TotalComponents.CechCup.component R X N p a n hpa x)) (TotalComponents.CechCup.component R X N q b m hqb y) +
      (-1 : ℤ) ^ n • TotalComponents.CechCup.cupInto R X N n (m + 1) (n + m + 1) (by omega)
        (TotalComponents.CechCup.component R X N p a n hpa x) ((TotalCup.Cech.total R X N).d m (m + 1) (TotalComponents.CechCup.component R X N q b m hqb y)) := by
  have hc := TotalCup.Cech.totalCup_ι R X N n m p a q b hpa hqb x y
  have hd := ComponentProducts.CechCup.differential_component_cup R X N p q a b (n + m) (by omega) x y
  have hleft := (congrArg ((TotalCup.Cech.total R X N).d (n + m) (n + m + 1)) hc).trans
    ((map_zsmul ((TotalCup.Cech.total R X N).d (n + m) (n + m + 1)).hom ((-1 : ℤ) ^ (a * q))
      (TotalComponents.CechCup.component R X N (p + q) (a + b) (n + m) (by omega) (CechCup.cup R X N p q a b x y))).trans
        (congrArg ((-1 : ℤ) ^ (a * q) • ·) hd))
  exact hleft.trans ((TotalProductSigns.product_rule p a q n hpa _ _ _ _).trans
    (congrArg₂ (fun z w => z + (-1 : ℤ) ^ n • w)
      (cupInto_differential_left_component R X N n m p a q b hpa hqb x y)
      (cupInto_differential_right_component R X N n m p a q b hpa hqb x y)).symm)

theorem differential_totalCup (n m : ℕ) (x : (TotalCup.Cech.total R X N).X n) (y : (TotalCup.Cech.total R X N).X m) :
    (TotalCup.Cech.total R X N).d (n + m) (n + m + 1) (TotalCup.Cech.totalCup R X N n m x y) =
      TotalComponents.CechCup.cupInto R X N (n + 1) m (n + m + 1) (by omega) ((TotalCup.Cech.total R X N).d n (n + 1) x) y +
      (-1 : ℤ) ^ n • TotalComponents.CechCup.cupInto R X N n (m + 1) (n + m + 1) (by omega) x ((TotalCup.Cech.total R X N).d m (m + 1) y) := by
  let L := (TotalCup.Cech.totalCup R X N n m).compr₂ ((TotalCup.Cech.total R X N).d (n + m) (n + m + 1)).hom
  let D := (TotalComponents.CechCup.cupInto R X N (n + 1) m (n + m + 1) (by omega)).compl₁₂
      ((TotalCup.Cech.total R X N).d n (n + 1)).hom LinearMap.id +
    (-1 : ℤ) ^ n • (TotalComponents.CechCup.cupInto R X N n (m + 1) (n + m + 1) (by omega)).compl₁₂
      LinearMap.id ((TotalCup.Cech.total R X N).d m (m + 1)).hom
  have h : L = D := by
    apply BicomplexPairing.bilinear_ext (TotalCup.Cech.bicomplex R X N) (TotalCup.Cech.bicomplex R X N) n m
    intro p a q b hpa hqb u v
    exact differential_totalCup_components R X N n m p a q b hpa hqb u v
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.TotalLeibniz.CechCup

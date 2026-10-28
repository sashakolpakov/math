import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.TotalD
import OAI.NumberTheory.PadicHodge.IntegralComparison.TotalProductSigns

/-! # Total Leibniz -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.TotalLeibniz.AlgebraicCechProduct

noncomputable section

/-! The full graded product rule on the original smooth Čech total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Simplicial

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  (N : SimplicialObject (FormalCoproduct.{0} X.left.Opens))

theorem cupInto_differential_left_component (n m p a q b : ℕ)
    (hpa : p + a = n) (hqb : q + b = m)
    (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj ⦋a⦌) (y : (AlgebraicSmoothCechProduct.smoothCochains X N q).obj ⦋b⦌) :
    TotalD.AlgebraicCechProduct.cupInto X N (n + 1) m (n + m + 1) (by omega)
        ((AlgebraicSmoothCechProduct.smoothTotal X N).d n (n + 1) (TotalD.AlgebraicCechProduct.component X N p a n hpa x)) (TotalD.AlgebraicCechProduct.component X N q b m hqb y) =
      (-1 : ℤ) ^ (a * q) • TotalD.AlgebraicCechProduct.component X N ((p + 1) + q) (a + b) (n + m + 1) (by omega)
        (AlgebraicSmoothCechProduct.cup X N (p + 1) q a b ((TotalD.AlgebraicCechProduct.deRhamDifferential X N p).app ⦋a⦌ x) y) +
      (-1 : ℤ) ^ p • ((-1 : ℤ) ^ ((a + 1) * q) •
        TotalD.AlgebraicCechProduct.component X N (p + q) ((a + 1) + b) (n + m + 1) (by omega)
          (AlgebraicSmoothCechProduct.cup X N p q (a + 1) b
            (Cosimplicial.BilinearCup.differential (AlgebraicSmoothCechProduct.smoothCochains X N p) a x) y)) := by
  let B := (TotalD.AlgebraicCechProduct.cupInto X N (n + 1) m (n + m + 1) (by omega)).flip
    (TotalD.AlgebraicCechProduct.component X N q b m hqb y)
  let u := TotalD.AlgebraicCechProduct.component X N (p + 1) a (n + 1) (by omega) ((TotalD.AlgebraicCechProduct.deRhamDifferential X N p).app ⦋a⦌ x)
  let v := TotalD.AlgebraicCechProduct.component X N p (a + 1) (n + 1) (by omega)
    (Cosimplicial.BilinearCup.differential (AlgebraicSmoothCechProduct.smoothCochains X N p) a x)
  have hs : B (u + (-1 : ℤ) ^ p • v) = B u + (-1 : ℤ) ^ p • B v :=
    (B.map_add u _).trans (congrArg (B u + ·) (map_zsmul B ((-1 : ℤ) ^ p) v))
  exact (congrArg B (TotalD.AlgebraicCechProduct.differential_component X N p a n hpa x)).trans
    (hs.trans (congrArg₂ (fun z w => z + (-1 : ℤ) ^ p • w)
      (TotalD.AlgebraicCechProduct.cupInto_component X N (n + 1) m (n + m + 1) (p + 1) a q b (by omega) (by omega) hqb
        ((TotalD.AlgebraicCechProduct.deRhamDifferential X N p).app ⦋a⦌ x) y)
      (TotalD.AlgebraicCechProduct.cupInto_component X N (n + 1) m (n + m + 1) p (a + 1) q b (by omega) (by omega) hqb
        (Cosimplicial.BilinearCup.differential (AlgebraicSmoothCechProduct.smoothCochains X N p) a x) y)))

theorem cupInto_differential_right_component (n m p a q b : ℕ)
    (hpa : p + a = n) (hqb : q + b = m)
    (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj ⦋a⦌) (y : (AlgebraicSmoothCechProduct.smoothCochains X N q).obj ⦋b⦌) :
    TotalD.AlgebraicCechProduct.cupInto X N n (m + 1) (n + m + 1) (by omega)
        (TotalD.AlgebraicCechProduct.component X N p a n hpa x) ((AlgebraicSmoothCechProduct.smoothTotal X N).d m (m + 1) (TotalD.AlgebraicCechProduct.component X N q b m hqb y)) =
      (-1 : ℤ) ^ (a * (q + 1)) • TotalD.AlgebraicCechProduct.component X N (p + (q + 1)) (a + b) (n + m + 1) (by omega)
        (AlgebraicSmoothCechProduct.cup X N p (q + 1) a b x ((TotalD.AlgebraicCechProduct.deRhamDifferential X N q).app ⦋b⦌ y)) +
      (-1 : ℤ) ^ q • ((-1 : ℤ) ^ (a * q) •
        TotalD.AlgebraicCechProduct.component X N (p + q) (a + (b + 1)) (n + m + 1) (by omega)
          (AlgebraicSmoothCechProduct.cup X N p q a (b + 1) x
            (Cosimplicial.BilinearCup.differential (AlgebraicSmoothCechProduct.smoothCochains X N q) b y))) := by
  let B := TotalD.AlgebraicCechProduct.cupInto X N n (m + 1) (n + m + 1) (by omega) (TotalD.AlgebraicCechProduct.component X N p a n hpa x)
  let u := TotalD.AlgebraicCechProduct.component X N (q + 1) b (m + 1) (by omega) ((TotalD.AlgebraicCechProduct.deRhamDifferential X N q).app ⦋b⦌ y)
  let v := TotalD.AlgebraicCechProduct.component X N q (b + 1) (m + 1) (by omega)
    (Cosimplicial.BilinearCup.differential (AlgebraicSmoothCechProduct.smoothCochains X N q) b y)
  have hs : B (u + (-1 : ℤ) ^ q • v) = B u + (-1 : ℤ) ^ q • B v :=
    (B.map_add u _).trans (congrArg (B u + ·) (map_zsmul B ((-1 : ℤ) ^ q) v))
  exact (congrArg B (TotalD.AlgebraicCechProduct.differential_component X N q b m hqb y)).trans
    (hs.trans (congrArg₂ (fun z w => z + (-1 : ℤ) ^ q • w)
      (TotalD.AlgebraicCechProduct.cupInto_component X N n (m + 1) (n + m + 1) p a (q + 1) b (by omega) hpa (by omega)
        x ((TotalD.AlgebraicCechProduct.deRhamDifferential X N q).app ⦋b⦌ y))
      (TotalD.AlgebraicCechProduct.cupInto_component X N n (m + 1) (n + m + 1) p a q (b + 1) (by omega) hpa (by omega)
        x (Cosimplicial.BilinearCup.differential (AlgebraicSmoothCechProduct.smoothCochains X N q) b y))))

theorem differential_totalPairing_components (n m p a q b : ℕ)
    (hpa : p + a = n) (hqb : q + b = m)
    (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj ⦋a⦌) (y : (AlgebraicSmoothCechProduct.smoothCochains X N q).obj ⦋b⦌) :
    (AlgebraicSmoothCechProduct.smoothTotal X N).d (n + m) (n + m + 1)
        (AlgebraicSmoothCechProduct.totalPairing X N n m (TotalD.AlgebraicCechProduct.component X N p a n hpa x) (TotalD.AlgebraicCechProduct.component X N q b m hqb y)) =
      TotalD.AlgebraicCechProduct.cupInto X N (n + 1) m (n + m + 1) (by omega)
        ((AlgebraicSmoothCechProduct.smoothTotal X N).d n (n + 1) (TotalD.AlgebraicCechProduct.component X N p a n hpa x)) (TotalD.AlgebraicCechProduct.component X N q b m hqb y) +
      (-1 : ℤ) ^ n • TotalD.AlgebraicCechProduct.cupInto X N n (m + 1) (n + m + 1) (by omega)
        (TotalD.AlgebraicCechProduct.component X N p a n hpa x) ((AlgebraicSmoothCechProduct.smoothTotal X N).d m (m + 1) (TotalD.AlgebraicCechProduct.component X N q b m hqb y)) := by
  have hc := TotalD.AlgebraicCechProduct.totalPairing_ι X N n m p a q b hpa hqb x y
  have hd := TotalD.AlgebraicCechProduct.differential_component_cup X N p q a b (n + m) (by omega) x y
  have hleft := (congrArg ((AlgebraicSmoothCechProduct.smoothTotal X N).d (n + m) (n + m + 1)) hc).trans
    ((map_zsmul ((AlgebraicSmoothCechProduct.smoothTotal X N).d (n + m) (n + m + 1)).hom ((-1 : ℤ) ^ (a * q))
      (TotalD.AlgebraicCechProduct.component X N (p + q) (a + b) (n + m) (by omega) (AlgebraicSmoothCechProduct.cup X N p q a b x y))).trans
        (congrArg ((-1 : ℤ) ^ (a * q) • ·) hd))
  exact hleft.trans ((TotalProductSigns.product_rule p a q n hpa _ _ _ _).trans
    (congrArg₂ (fun z w => z + (-1 : ℤ) ^ n • w)
      (cupInto_differential_left_component X N n m p a q b hpa hqb x y)
      (cupInto_differential_right_component X N n m p a q b hpa hqb x y)).symm)

theorem differential_totalPairing (n m : ℕ) (x : (AlgebraicSmoothCechProduct.smoothTotal X N).X n) (y : (AlgebraicSmoothCechProduct.smoothTotal X N).X m) :
    (AlgebraicSmoothCechProduct.smoothTotal X N).d (n + m) (n + m + 1) (AlgebraicSmoothCechProduct.totalPairing X N n m x y) =
      TotalD.AlgebraicCechProduct.cupInto X N (n + 1) m (n + m + 1) (by omega) ((AlgebraicSmoothCechProduct.smoothTotal X N).d n (n + 1) x) y +
      (-1 : ℤ) ^ n • TotalD.AlgebraicCechProduct.cupInto X N n (m + 1) (n + m + 1) (by omega) x ((AlgebraicSmoothCechProduct.smoothTotal X N).d m (m + 1) y) := by
  let L := (AlgebraicSmoothCechProduct.totalPairing X N n m).compr₂ ((AlgebraicSmoothCechProduct.smoothTotal X N).d (n + m) (n + m + 1)).hom
  let D := (TotalD.AlgebraicCechProduct.cupInto X N (n + 1) m (n + m + 1) (by omega)).compl₁₂
      ((AlgebraicSmoothCechProduct.smoothTotal X N).d n (n + 1)).hom LinearMap.id +
    (-1 : ℤ) ^ n • (TotalD.AlgebraicCechProduct.cupInto X N n (m + 1) (n + m + 1) (by omega)).compl₁₂
      LinearMap.id ((AlgebraicSmoothCechProduct.smoothTotal X N).d m (m + 1)).hom
  have h : L = D := by
    apply BicomplexPairing.bilinear_ext (AlgebraicSmoothCechProduct.smoothBicomplex X N) (AlgebraicSmoothCechProduct.smoothBicomplex X N) n m
    intro p a q b hpa hqb u v
    exact differential_totalPairing_components X N n m p a q b hpa hqb u v
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.TotalLeibniz.AlgebraicCechProduct

import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ComponentProducts
import OAI.NumberTheory.PadicHodge.IntegralComparison.TotalProductSigns

/-! # Total Leibniz -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalLeibniz.CechProduct

noncomputable section

/-! The graded Leibniz rule for the actual total presheaf Čech product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

universe u v w t r

variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  (N : SimplicialObject (FormalCoproduct.{w} C))
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max w t} R) ℕ)
  (μ : ∀ p q (U : Cᵒᵖ), (P.X p).obj U →ₗ[R]
    (P.X q).obj U →ₗ[R] (P.X (p + q)).obj U)

variable
  (hμ : ∀ p q {U V : Cᵒᵖ} (f : U ⟶ V) (x : (P.X p).obj U) (y : (P.X q).obj U),
    (P.X (p + q)).map f (μ p q U x y) = μ p q V ((P.X p).map f x) ((P.X q).map f y))
  (dμ : ∀ p q (U : Cᵒᵖ) (x : (P.X p).obj U) (y : (P.X q).obj U),
    (P.d (p + q) (p + q + 1)).app U (μ p q U x y) =
      CechProduct.sectionDegreeCast P (by omega : (p + 1) + q = p + q + 1) U
        (μ (p + 1) q U ((P.d p (p + 1)).app U x) y) +
      (-1 : ℤ) ^ p • CechProduct.sectionDegreeCast P (by omega : p + (q + 1) = p + q + 1) U
        (μ p (q + 1) U x ((P.d q (q + 1)).app U y)))

theorem cupInto_differential_left_component (n m p a q b : ℕ)
    (hpa : p + a = n) (hqb : q + b = m)
    (x : (CechProduct.cochains N P p).obj ⦋a⦌) (y : (CechProduct.cochains N P q).obj ⦋b⦌) :
    TotalComponents.CechProduct.cupInto N P μ (n + 1) m (n + m + 1) (by omega)
        ((TotalCup.CechProduct.total N P).d n (n + 1) (TotalComponents.CechProduct.component N P p a n hpa x)) (TotalComponents.CechProduct.component N P q b m hqb y) =
      (-1 : ℤ) ^ (a * q) • TotalComponents.CechProduct.component N P ((p + 1) + q) (a + b) (n + m + 1) (by omega)
        (CechProduct.cup N P μ (p + 1) q a b ((CechDifferential.Product.presheafDifferential N P p).app ⦋a⦌ x) y) +
      (-1 : ℤ) ^ p • ((-1 : ℤ) ^ ((a + 1) * q) •
        TotalComponents.CechProduct.component N P (p + q) ((a + 1) + b) (n + m + 1) (by omega)
          (CechProduct.cup N P μ p q (a + 1) b
            (Cosimplicial.BilinearCup.differential (CechProduct.cochains N P p) a x) y)) := by
  let B := (TotalComponents.CechProduct.cupInto N P μ (n + 1) m (n + m + 1) (by omega)).flip
    (TotalComponents.CechProduct.component N P q b m hqb y)
  let u := TotalComponents.CechProduct.component N P (p + 1) a (n + 1) (by omega) ((CechDifferential.Product.presheafDifferential N P p).app ⦋a⦌ x)
  let v := TotalComponents.CechProduct.component N P p (a + 1) (n + 1) (by omega)
    (Cosimplicial.BilinearCup.differential (CechProduct.cochains N P p) a x)
  have hs : B (u + (-1 : ℤ) ^ p • v) = B u + (-1 : ℤ) ^ p • B v :=
    (B.map_add u _).trans (congrArg (B u + ·) (map_zsmul B ((-1 : ℤ) ^ p) v))
  exact (congrArg B (TotalComponents.CechProduct.differential_component N P p a n hpa x)).trans
    (hs.trans (congrArg₂ (fun z w => z + (-1 : ℤ) ^ p • w)
      (TotalComponents.CechProduct.cupInto_component N P μ (n + 1) m (n + m + 1) (p + 1) a q b (by omega) (by omega) hqb
        ((CechDifferential.Product.presheafDifferential N P p).app ⦋a⦌ x) y)
      (TotalComponents.CechProduct.cupInto_component N P μ (n + 1) m (n + m + 1) p (a + 1) q b (by omega) (by omega) hqb
        (Cosimplicial.BilinearCup.differential (CechProduct.cochains N P p) a x) y)))

theorem cupInto_differential_right_component (n m p a q b : ℕ)
    (hpa : p + a = n) (hqb : q + b = m)
    (x : (CechProduct.cochains N P p).obj ⦋a⦌) (y : (CechProduct.cochains N P q).obj ⦋b⦌) :
    TotalComponents.CechProduct.cupInto N P μ n (m + 1) (n + m + 1) (by omega)
        (TotalComponents.CechProduct.component N P p a n hpa x) ((TotalCup.CechProduct.total N P).d m (m + 1) (TotalComponents.CechProduct.component N P q b m hqb y)) =
      (-1 : ℤ) ^ (a * (q + 1)) • TotalComponents.CechProduct.component N P (p + (q + 1)) (a + b) (n + m + 1) (by omega)
        (CechProduct.cup N P μ p (q + 1) a b x ((CechDifferential.Product.presheafDifferential N P q).app ⦋b⦌ y)) +
      (-1 : ℤ) ^ q • ((-1 : ℤ) ^ (a * q) •
        TotalComponents.CechProduct.component N P (p + q) (a + (b + 1)) (n + m + 1) (by omega)
          (CechProduct.cup N P μ p q a (b + 1) x
            (Cosimplicial.BilinearCup.differential (CechProduct.cochains N P q) b y))) := by
  let B := TotalComponents.CechProduct.cupInto N P μ n (m + 1) (n + m + 1) (by omega) (TotalComponents.CechProduct.component N P p a n hpa x)
  let u := TotalComponents.CechProduct.component N P (q + 1) b (m + 1) (by omega) ((CechDifferential.Product.presheafDifferential N P q).app ⦋b⦌ y)
  let v := TotalComponents.CechProduct.component N P q (b + 1) (m + 1) (by omega)
    (Cosimplicial.BilinearCup.differential (CechProduct.cochains N P q) b y)
  have hs : B (u + (-1 : ℤ) ^ q • v) = B u + (-1 : ℤ) ^ q • B v :=
    (B.map_add u _).trans (congrArg (B u + ·) (map_zsmul B ((-1 : ℤ) ^ q) v))
  exact (congrArg B (TotalComponents.CechProduct.differential_component N P q b m hqb y)).trans
    (hs.trans (congrArg₂ (fun z w => z + (-1 : ℤ) ^ q • w)
      (TotalComponents.CechProduct.cupInto_component N P μ n (m + 1) (n + m + 1) p a (q + 1) b (by omega) hpa (by omega)
        x ((CechDifferential.Product.presheafDifferential N P q).app ⦋b⦌ y))
      (TotalComponents.CechProduct.cupInto_component N P μ n (m + 1) (n + m + 1) p a q (b + 1) (by omega) hpa (by omega)
        x (Cosimplicial.BilinearCup.differential (CechProduct.cochains N P q) b y))))

include hμ dμ in
theorem differential_totalCup_components (n m p a q b : ℕ)
    (hpa : p + a = n) (hqb : q + b = m)
    (x : (CechProduct.cochains N P p).obj ⦋a⦌) (y : (CechProduct.cochains N P q).obj ⦋b⦌) :
    (TotalCup.CechProduct.total N P).d (n + m) (n + m + 1)
        (TotalCup.CechProduct.totalCup N P μ n m (TotalComponents.CechProduct.component N P p a n hpa x) (TotalComponents.CechProduct.component N P q b m hqb y)) =
      TotalComponents.CechProduct.cupInto N P μ (n + 1) m (n + m + 1) (by omega)
        ((TotalCup.CechProduct.total N P).d n (n + 1) (TotalComponents.CechProduct.component N P p a n hpa x)) (TotalComponents.CechProduct.component N P q b m hqb y) +
      (-1 : ℤ) ^ n • TotalComponents.CechProduct.cupInto N P μ n (m + 1) (n + m + 1) (by omega)
        (TotalComponents.CechProduct.component N P p a n hpa x) ((TotalCup.CechProduct.total N P).d m (m + 1) (TotalComponents.CechProduct.component N P q b m hqb y)) := by
  have hc := TotalCup.CechProduct.totalCup_ι N P μ n m p a q b hpa hqb x y
  have hd := ComponentProducts.CechProduct.differential_component_cup N P μ hμ dμ p q a b (n + m) (by omega) x y
  have hleft := (congrArg ((TotalCup.CechProduct.total N P).d (n + m) (n + m + 1)) hc).trans
    ((map_zsmul ((TotalCup.CechProduct.total N P).d (n + m) (n + m + 1)).hom ((-1 : ℤ) ^ (a * q))
      (TotalComponents.CechProduct.component N P (p + q) (a + b) (n + m) (by omega) (CechProduct.cup N P μ p q a b x y))).trans
        (congrArg ((-1 : ℤ) ^ (a * q) • ·) hd))
  exact hleft.trans ((TotalProductSigns.product_rule p a q n hpa _ _ _ _).trans
    (congrArg₂ (fun z w => z + (-1 : ℤ) ^ n • w)
      (cupInto_differential_left_component N P μ n m p a q b hpa hqb x y)
      (cupInto_differential_right_component N P μ n m p a q b hpa hqb x y)).symm)

include hμ dμ in
theorem differential_totalCup (n m : ℕ) (x : (TotalCup.CechProduct.total N P).X n) (y : (TotalCup.CechProduct.total N P).X m) :
    (TotalCup.CechProduct.total N P).d (n + m) (n + m + 1) (TotalCup.CechProduct.totalCup N P μ n m x y) =
      TotalComponents.CechProduct.cupInto N P μ (n + 1) m (n + m + 1) (by omega) ((TotalCup.CechProduct.total N P).d n (n + 1) x) y +
      (-1 : ℤ) ^ n • TotalComponents.CechProduct.cupInto N P μ n (m + 1) (n + m + 1) (by omega) x ((TotalCup.CechProduct.total N P).d m (m + 1) y) := by
  let L := (TotalCup.CechProduct.totalCup N P μ n m).compr₂ ((TotalCup.CechProduct.total N P).d (n + m) (n + m + 1)).hom
  let D := (TotalComponents.CechProduct.cupInto N P μ (n + 1) m (n + m + 1) (by omega)).compl₁₂
      ((TotalCup.CechProduct.total N P).d n (n + 1)).hom LinearMap.id +
    (-1 : ℤ) ^ n • (TotalComponents.CechProduct.cupInto N P μ n (m + 1) (n + m + 1) (by omega)).compl₁₂
      LinearMap.id ((TotalCup.CechProduct.total N P).d m (m + 1)).hom
  have h : L = D := by
    apply BicomplexPairing.bilinear_ext (TotalCup.CechProduct.bicomplex N P) (TotalCup.CechProduct.bicomplex N P) n m
    intro p a q b hpa hqb u v
    exact differential_totalCup_components N P μ hμ dμ n m p a q b hpa hqb u v
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalLeibniz.CechProduct

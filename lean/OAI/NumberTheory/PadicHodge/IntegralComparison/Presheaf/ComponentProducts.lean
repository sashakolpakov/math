import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalComponents

/-! # Component Products -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ComponentProducts.CechProduct

noncomputable section

/-! Product rules in each bidegree after inclusion into the actual
total complex. Degree casts are eliminated by the same inclusion maps. -/

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

include dμ in
theorem component_presheafDifferential_cup (p q a b k : ℕ) (hk : p + q + 1 + (a + b) = k)
    (x : (CechProduct.cochains N P p).obj ⦋a⦌) (y : (CechProduct.cochains N P q).obj ⦋b⦌) :
    TotalComponents.CechProduct.component N P (p + q + 1) (a + b) k hk
        ((CechDifferential.Product.presheafDifferential N P (p + q)).app ⦋a + b⦌ (CechProduct.cup N P μ p q a b x y)) =
      TotalComponents.CechProduct.component N P ((p + 1) + q) (a + b) k (by omega)
        (CechProduct.cup N P μ (p + 1) q a b ((CechDifferential.Product.presheafDifferential N P p).app ⦋a⦌ x) y) +
      (-1 : ℤ) ^ p • TotalComponents.CechProduct.component N P (p + (q + 1)) (a + b) k (by omega)
        (CechProduct.cup N P μ p (q + 1) a b x ((CechDifferential.Product.presheafDifferential N P q).app ⦋b⦌ y)) := by
  rw [CechDifferential.Product.presheafDifferential_cup N P μ dμ]
  erw [map_add, map_zsmul, TotalComponents.CechProduct.component_formDegreeCast, TotalComponents.CechProduct.component_formDegreeCast]
  all_goals omega

include hμ in
theorem component_cechDifferential_cup (p q a b k : ℕ) (hk : (p + q) + (a + b + 1) = k)
    (x : (CechProduct.cochains N P p).obj ⦋a⦌) (y : (CechProduct.cochains N P q).obj ⦋b⦌) :
    TotalComponents.CechProduct.component N P (p + q) (a + b + 1) k hk
        (Cosimplicial.BilinearCup.differential (CechProduct.cochains N P (p + q)) (a + b)
          (CechProduct.cup N P μ p q a b x y)) =
      TotalComponents.CechProduct.component N P (p + q) ((a + 1) + b) k (by omega)
        (CechProduct.cup N P μ p q (a + 1) b
          (Cosimplicial.BilinearCup.differential (CechProduct.cochains N P p) a x) y) +
      (-1 : ℤ) ^ a • TotalComponents.CechProduct.component N P (p + q) (a + (b + 1)) k (by omega)
        (CechProduct.cup N P μ p q a (b + 1) x
          (Cosimplicial.BilinearCup.differential (CechProduct.cochains N P q) b y)) := by
  have hc : Cosimplicial.BilinearCup.differential (CechProduct.cochains N P (p + q)) (a + b)
      (CechProduct.cup N P μ p q a b x y) =
        Cosimplicial.BilinearDegrees.Cup.degreeCast (CechProduct.cochains N P (p + q))
          (by omega : (a + 1) + b = a + b + 1)
          (CechProduct.cup N P μ p q (a + 1) b
            (Cosimplicial.BilinearCup.differential (CechProduct.cochains N P p) a x) y) +
        (-1 : ℤ) ^ a • Cosimplicial.BilinearDegrees.Cup.degreeCast (CechProduct.cochains N P (p + q))
          (by omega : a + (b + 1) = a + b + 1)
          (CechProduct.cup N P μ p q a (b + 1) x
            (Cosimplicial.BilinearCup.differential (CechProduct.cochains N P q) b y)) :=
    Cosimplicial.BilinearDegrees.Cup.differential_cup_cast _ _ _ (CechProduct.pairing N P μ p q)
      (CechProduct.pairing_natural N P μ hμ p q) a b x y
  rw [hc]
  erw [map_add, map_zsmul, TotalComponents.CechProduct.component_cechDegreeCast, TotalComponents.CechProduct.component_cechDegreeCast]
  all_goals omega

include hμ dμ in
theorem differential_component_cup (p q a b k : ℕ) (hk : (p + q) + (a + b) = k)
    (x : (CechProduct.cochains N P p).obj ⦋a⦌) (y : (CechProduct.cochains N P q).obj ⦋b⦌) :
    (TotalCup.CechProduct.total N P).d k (k + 1)
        (TotalComponents.CechProduct.component N P (p + q) (a + b) k hk (CechProduct.cup N P μ p q a b x y)) =
      (TotalComponents.CechProduct.component N P ((p + 1) + q) (a + b) (k + 1) (by omega)
          (CechProduct.cup N P μ (p + 1) q a b ((CechDifferential.Product.presheafDifferential N P p).app ⦋a⦌ x) y) +
        (-1 : ℤ) ^ p • TotalComponents.CechProduct.component N P (p + (q + 1)) (a + b) (k + 1) (by omega)
          (CechProduct.cup N P μ p (q + 1) a b x ((CechDifferential.Product.presheafDifferential N P q).app ⦋b⦌ y))) +
      (-1 : ℤ) ^ (p + q) •
        (TotalComponents.CechProduct.component N P (p + q) ((a + 1) + b) (k + 1) (by omega)
            (CechProduct.cup N P μ p q (a + 1) b
              (Cosimplicial.BilinearCup.differential (CechProduct.cochains N P p) a x) y) +
          (-1 : ℤ) ^ a • TotalComponents.CechProduct.component N P (p + q) (a + (b + 1)) (k + 1) (by omega)
            (CechProduct.cup N P μ p q a (b + 1) x
              (Cosimplicial.BilinearCup.differential (CechProduct.cochains N P q) b y))) := by
  rw [TotalComponents.CechProduct.differential_component, component_presheafDifferential_cup N P μ dμ, component_cechDifferential_cup N P μ hμ]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ComponentProducts.CechProduct

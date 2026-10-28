import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BilinearPairing
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total

/-! # Cech Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CechProduct

noncomputable section

/-! Native Čech products for a complex of module presheaves. The pairing
is evaluated on the actual categorical products of the given cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v w t r

variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  (N : SimplicialObject (FormalCoproduct.{w} C))
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max w t} R) ℕ)

def sectionDegreeCast (Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{t} R) ℕ)
    {p q : ℕ} (h : p = q) (U : Cᵒᵖ) :
    (Q.X p).obj U ≃ₗ[R] (Q.X q).obj U := h ▸ LinearEquiv.refl R ((Q.X p).obj U)

def cochains (p : ℕ) : CosimplicialObject (ModuleCat.{max w t} R) :=
  Cech.BilinearPairing.cosimplicial N (P.X p)

variable (μ : ∀ p q (U : Cᵒᵖ), (P.X p).obj U →ₗ[R]
  (P.X q).obj U →ₗ[R] (P.X (p + q)).obj U)

def pairing (p q : ℕ) (n : SimplexCategory) :
    (cochains N P p).obj n →ₗ[R] (cochains N P q).obj n →ₗ[R]
      (cochains N P (p + q)).obj n :=
  Cech.BilinearPairing.pairing N (P.X p) (P.X q) (P.X (p + q)) (μ p q) n

def cup (p q a b : ℕ) :
    (cochains N P p).obj ⦋a⦌ →ₗ[R] (cochains N P q).obj ⦋b⦌ →ₗ[R]
      (cochains N P (p + q)).obj ⦋a + b⦌ :=
  Cosimplicial.BilinearCup.cup (cochains N P p) (cochains N P q)
    (cochains N P (p + q)) (pairing N P μ p q) a b

variable (hμ : ∀ p q {U V : Cᵒᵖ} (f : U ⟶ V) (x : (P.X p).obj U) (y : (P.X q).obj U),
  (P.X (p + q)).map f (μ p q U x y) = μ p q V ((P.X p).map f x) ((P.X q).map f y))

include hμ in
theorem pairing_natural (p q : ℕ) {n m : SimplexCategory} (f : n ⟶ m)
    (x : (cochains N P p).obj n) (y : (cochains N P q).obj n) :
    (cochains N P (p + q)).map f (pairing N P μ p q n x y) =
      pairing N P μ p q m ((cochains N P p).map f x) ((cochains N P q).map f y) :=
  Cech.BilinearPairing.pairing_natural N _ _ _ (μ p q) (hμ p q) f x y

include hμ in
theorem differential_cup (p q a b : ℕ)
    (x : (cochains N P p).obj ⦋a⦌) (y : (cochains N P q).obj ⦋b⦌) :
    Cosimplicial.BilinearCup.differential (cochains N P (p + q)) (a + b)
        (cup N P μ p q a b x y) =
      pairing N P μ p q ⦋a + b + 1⦌
        ((cochains N P p).map
          (SimplexCategory.subinterval 0 (a + 1) (by omega : 0 + (a + 1) ≤ a + b + 1))
          (Cosimplicial.BilinearCup.differential (cochains N P p) a x))
        ((cochains N P q).map
          (SimplexCategory.subinterval (a + 1) b (by omega : (a + 1) + b ≤ a + b + 1)) y) +
      (-1 : ℤ) ^ a • pairing N P μ p q ⦋a + b + 1⦌
        ((cochains N P p).map
          (SimplexCategory.subinterval 0 a (by omega : 0 + a ≤ a + b + 1)) x)
        ((cochains N P q).map
          (SimplexCategory.subinterval a (b + 1) (by omega : a + (b + 1) ≤ a + b + 1))
          (Cosimplicial.BilinearCup.differential (cochains N P q) b y)) :=
  Cosimplicial.BilinearCup.differential_cup _ _ _ (pairing N P μ p q)
    (pairing_natural N P μ hμ p q) a b x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CechProduct

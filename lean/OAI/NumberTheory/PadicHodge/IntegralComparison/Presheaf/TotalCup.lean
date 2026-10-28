import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CechDifferential
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.BilinearDegrees
import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexPairing
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total

/-! # Total Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalCup.CechProduct

noncomputable section

/-! The signed exterior/Alexander–Whitney product on the given
categorical Čech total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

universe u v w t r

variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  (N : SimplicialObject (FormalCoproduct.{w} C))
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max w t} R) ℕ)
  (μ : ∀ p q (U : Cᵒᵖ), (P.X p).obj U →ₗ[R]
    (P.X q).obj U →ₗ[R] (P.X (p + q)).obj U)

def bicomplex : HomologicalComplex₂ (ModuleCat.{max w t} R) (.up ℕ) (.up ℕ) :=
  CechCoefficient.Total.bicomplex N P

def total : CochainComplex (ModuleCat.{max w t} R) ℕ := (bicomplex N P).total (.up ℕ)

def signedPairing (p a q b : ℕ) :
    ((bicomplex N P).X p).X a →ₗ[R] ((bicomplex N P).X q).X b →ₗ[R]
      ((bicomplex N P).X (p + q)).X (a + b) :=
  (-1 : ℤ) ^ (a * q) • CechProduct.cup N P μ p q a b

def totalCup (n m : ℕ) : (CechProduct.total N P).X n →ₗ[R] (CechProduct.total N P).X m →ₗ[R]
    (CechProduct.total N P).X (n + m) :=
  BicomplexPairing.totalPairing (bicomplex N P) (bicomplex N P) (bicomplex N P)
    (signedPairing N P μ) n m

theorem totalCup_ι (n m p a q b : ℕ) (hpa : p + a = n) (hqb : q + b = m)
    (x : ((bicomplex N P).X p).X a) (y : ((bicomplex N P).X q).X b) :
    totalCup N P μ n m ((bicomplex N P).ιTotal (.up ℕ) p a n hpa x)
        ((bicomplex N P).ιTotal (.up ℕ) q b m hqb y) =
      (-1 : ℤ) ^ (a * q) •
        (bicomplex N P).ιTotal (.up ℕ) (p + q) (a + b) (n + m) (by
          change (p + q) + (a + b) = n + m
          omega) (CechProduct.cup N P μ p q a b x y) := by
  exact (BicomplexPairing.totalPairing_ι _ _ _ (signedPairing N P μ)
    n m p a q b hpa hqb x y).trans (map_zsmul
      ((bicomplex N P).ιTotal (.up ℕ) (p + q) (a + b) (n + m) (by
        change (p + q) + (a + b) = n + m
        omega)).hom ((-1 : ℤ) ^ (a * q)) (CechProduct.cup N P μ p q a b x y))

theorem bicomplex_d_form_apply (p a : ℕ) (x : ((bicomplex N P).X p).X a) :
    ((bicomplex N P).d p (p + 1)).f a x = (CechDifferential.Product.presheafDifferential N P p).app ⦋a⦌ x := rfl

theorem bicomplex_d_cech_apply (p a : ℕ) (x : ((bicomplex N P).X p).X a) :
    ((bicomplex N P).X p).d a (a + 1) x =
      Cosimplicial.BilinearCup.differential (CechProduct.cochains N P p) a x :=
  Cosimplicial.BilinearCup.complex_d_apply (CechProduct.cochains N P p) a x

theorem formDegreeCast_ι {p q a n : ℕ} (h : p = q) (hpa : p + a = n) (hqa : q + a = n)
    (x : ((bicomplex N P).X p).X a) :
    (bicomplex N P).ιTotal (.up ℕ) q a n hqa (CechDifferential.Product.formDegreeCast N P h ⦋a⦌ x) =
      (bicomplex N P).ιTotal (.up ℕ) p a n hpa x := by
  subst q
  rfl

theorem cechDegreeCast_ι {p a b n : ℕ} (h : a = b) (hpa : p + a = n) (hpb : p + b = n)
    (x : ((bicomplex N P).X p).X a) :
    (bicomplex N P).ιTotal (.up ℕ) p b n hpb
        (Cosimplicial.BilinearDegrees.Cup.degreeCast (CechProduct.cochains N P p) h x) =
      (bicomplex N P).ιTotal (.up ℕ) p a n hpa x := by
  subst b
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalCup.CechProduct

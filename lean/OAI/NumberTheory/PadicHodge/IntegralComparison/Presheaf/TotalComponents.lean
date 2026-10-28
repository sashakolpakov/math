import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalCup

/-! # Total Components -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalComponents.CechProduct

noncomputable section

/-! Component formulas for the differential and the cup product of
the given Čech total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

universe u v w t r

variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  (N : SimplicialObject (FormalCoproduct.{w} C))
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max w t} R) ℕ)
  (μ : ∀ p q (U : Cᵒᵖ), (P.X p).obj U →ₗ[R]
    (P.X q).obj U →ₗ[R] (P.X (p + q)).obj U)

def component (p a n : ℕ) (h : p + a = n) :
    (CechProduct.cochains N P p).obj ⦋a⦌ →ₗ[R] (TotalCup.CechProduct.total N P).X n :=
  ((TotalCup.CechProduct.bicomplex N P).ιTotal (.up ℕ) p a n h).hom

def totalDegreeCast {n m : ℕ} (h : n = m) : (TotalCup.CechProduct.total N P).X n ≃ₗ[R] (TotalCup.CechProduct.total N P).X m :=
  h ▸ LinearEquiv.refl R ((TotalCup.CechProduct.total N P).X n)

def cupInto (n m k : ℕ) (h : n + m = k) :
    (TotalCup.CechProduct.total N P).X n →ₗ[R] (TotalCup.CechProduct.total N P).X m →ₗ[R] (TotalCup.CechProduct.total N P).X k :=
  (TotalCup.CechProduct.totalCup N P μ n m).compr₂ (totalDegreeCast N P h).toLinearMap

theorem cupInto_component (n m k p a q b : ℕ) (hnm : n + m = k)
    (hpa : p + a = n) (hqb : q + b = m)
    (x : (CechProduct.cochains N P p).obj ⦋a⦌) (y : (CechProduct.cochains N P q).obj ⦋b⦌) :
    cupInto N P μ n m k hnm (component N P p a n hpa x) (component N P q b m hqb y) =
      (-1 : ℤ) ^ (a * q) • component N P (p + q) (a + b) k (by omega)
        (CechProduct.cup N P μ p q a b x y) := by
  subst k
  exact TotalCup.CechProduct.totalCup_ι N P μ n m p a q b hpa hqb x y

theorem totalDegreeCast_component {p a n m : ℕ} (h : n = m) (hpa : p + a = n)
    (hpa' : p + a = m) (x : (CechProduct.cochains N P p).obj ⦋a⦌) :
    totalDegreeCast N P h (component N P p a n hpa x) = component N P p a m hpa' x := by
  subst m
  rfl

theorem component_formDegreeCast {p q a n : ℕ} (h : p = q) (hpa : p + a = n) (hqa : q + a = n)
    (x : (CechProduct.cochains N P p).obj ⦋a⦌) :
    component N P q a n hqa (CechDifferential.Product.formDegreeCast N P h ⦋a⦌ x) = component N P p a n hpa x := by
  subst q
  rfl

theorem component_cechDegreeCast {p a b n : ℕ} (h : a = b) (hpa : p + a = n) (hpb : p + b = n)
    (x : (CechProduct.cochains N P p).obj ⦋a⦌) :
    component N P p b n hpb (Cosimplicial.BilinearDegrees.Cup.degreeCast (CechProduct.cochains N P p) h x) =
      component N P p a n hpa x := by
  subst b
  rfl

theorem differential_component (p a n : ℕ) (hpa : p + a = n) (x : (CechProduct.cochains N P p).obj ⦋a⦌) :
    (TotalCup.CechProduct.total N P).d n (n + 1) (component N P p a n hpa x) =
      component N P (p + 1) a (n + 1) (by omega) ((CechDifferential.Product.presheafDifferential N P p).app ⦋a⦌ x) +
      (-1 : ℤ) ^ p • component N P p (a + 1) (n + 1) (by omega)
        (Cosimplicial.BilinearCup.differential (CechProduct.cochains N P p) a x) := by
  have h := ConcreteCategory.congr_hom (AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.ιTotal_d_of_sum (TotalCup.CechProduct.bicomplex N P) p a n hpa) x
  simp only [Units.smul_def] at h
  change (TotalCup.CechProduct.total N P).d n (n + 1) (component N P p a n hpa x) =
    component N P (p + 1) a (n + 1) (by omega) (((TotalCup.CechProduct.bicomplex N P).d p (p + 1)).f a x) +
      (-1 : ℤ) ^ p • component N P p (a + 1) (n + 1) (by omega)
        (((TotalCup.CechProduct.bicomplex N P).X p).d a (a + 1) x) at h
  exact h.trans (congrArg₂ (· + ·)
    (congrArg (component N P (p + 1) a (n + 1) (by omega))
      (TotalCup.CechProduct.bicomplex_d_form_apply N P p a x))
    (congrArg (fun z => (-1 : ℤ) ^ p • component N P p (a + 1) (n + 1) (by omega) z)
      (TotalCup.CechProduct.bicomplex_d_cech_apply N P p a x)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalComponents.CechProduct

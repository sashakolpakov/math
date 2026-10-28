import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.TotalCup

/-! # Total Components -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.TotalComponents.CechCup

noncomputable section

/-! Component formulas for the differential and the cup product of
the original Čech–de Rham total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Simplicial

universe u

variable (R : Type u) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R)))
  (N : SimplicialObject (FormalCoproduct.{u} X.left.Opens))

def component (p a n : ℕ) (h : p + a = n) :
    (CechCup.cochains R X N p).obj ⦋a⦌ →ₗ[R] (TotalCup.Cech.total R X N).X n :=
  ((TotalCup.Cech.bicomplex R X N).ιTotal (.up ℕ) p a n h).hom

def totalDegreeCast {n m : ℕ} (h : n = m) : (TotalCup.Cech.total R X N).X n ≃ₗ[R] (TotalCup.Cech.total R X N).X m :=
  h ▸ LinearEquiv.refl R ((TotalCup.Cech.total R X N).X n)

def cupInto (n m k : ℕ) (h : n + m = k) :
    (TotalCup.Cech.total R X N).X n →ₗ[R] (TotalCup.Cech.total R X N).X m →ₗ[R] (TotalCup.Cech.total R X N).X k :=
  (TotalCup.Cech.totalCup R X N n m).compr₂ (totalDegreeCast R X N h).toLinearMap

theorem cupInto_component (n m k p a q b : ℕ) (hnm : n + m = k)
    (hpa : p + a = n) (hqb : q + b = m)
    (x : (CechCup.cochains R X N p).obj ⦋a⦌) (y : (CechCup.cochains R X N q).obj ⦋b⦌) :
    cupInto R X N n m k hnm (component R X N p a n hpa x) (component R X N q b m hqb y) =
      (-1 : ℤ) ^ (a * q) • component R X N (p + q) (a + b) k (by omega)
        (CechCup.cup R X N p q a b x y) := by
  subst k
  exact TotalCup.Cech.totalCup_ι R X N n m p a q b hpa hqb x y

omit [Algebra ℚ R] in
theorem totalDegreeCast_component {p a n m : ℕ} (h : n = m) (hpa : p + a = n)
    (hpa' : p + a = m) (x : (CechCup.cochains R X N p).obj ⦋a⦌) :
    totalDegreeCast R X N h (component R X N p a n hpa x) = component R X N p a m hpa' x := by
  subst m
  rfl

omit [Algebra ℚ R] in
theorem component_formDegreeCast {p q a n : ℕ} (h : p = q) (hpa : p + a = n) (hqa : q + a = n)
    (x : (CechCup.cochains R X N p).obj ⦋a⦌) :
    component R X N q a n hqa (CechDifferential.Cup.formDegreeCast R X N h ⦋a⦌ x) = component R X N p a n hpa x := by
  subst q
  rfl

omit [Algebra ℚ R] in
theorem component_cechDegreeCast {p a b n : ℕ} (h : a = b) (hpa : p + a = n) (hpb : p + b = n)
    (x : (CechCup.cochains R X N p).obj ⦋a⦌) :
    component R X N p b n hpb (Cosimplicial.BilinearDegrees.Cup.degreeCast (CechCup.cochains R X N p) h x) =
      component R X N p a n hpa x := by
  subst b
  rfl

omit [Algebra ℚ R] in
theorem differential_component (p a n : ℕ) (hpa : p + a = n) (x : (CechCup.cochains R X N p).obj ⦋a⦌) :
    (TotalCup.Cech.total R X N).d n (n + 1) (component R X N p a n hpa x) =
      component R X N (p + 1) a (n + 1) (by omega) ((CechDifferential.Cup.deRhamDifferential R X N p).app ⦋a⦌ x) +
      (-1 : ℤ) ^ p • component R X N p (a + 1) (n + 1) (by omega)
        (Cosimplicial.BilinearCup.differential (CechCup.cochains R X N p) a x) := by
  have h := ConcreteCategory.congr_hom (AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.ιTotal_d_of_sum (TotalCup.Cech.bicomplex R X N) p a n hpa) x
  simp only [Units.smul_def] at h
  change (TotalCup.Cech.total R X N).d n (n + 1) (component R X N p a n hpa x) =
    component R X N (p + 1) a (n + 1) (by omega) (((TotalCup.Cech.bicomplex R X N).d p (p + 1)).f a x) +
      (-1 : ℤ) ^ p • component R X N p (a + 1) (n + 1) (by omega)
        (((TotalCup.Cech.bicomplex R X N).X p).d a (a + 1) x) at h
  exact h.trans (congrArg₂ (· + ·)
    (congrArg (component R X N (p + 1) a (n + 1) (by omega))
      (TotalCup.Cech.bicomplex_d_form_apply R X N p a x))
    (congrArg (fun z => (-1 : ℤ) ^ p • component R X N p (a + 1) (n + 1) (by omega) z)
      (TotalCup.Cech.bicomplex_d_cech_apply R X N p a x)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.TotalComponents.CechCup

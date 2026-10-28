import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CechDifferential
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.BilinearDegrees
import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexPairing
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total

/-! # Total Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.TotalCup.Cech

noncomputable section

/-! The signed exterior/Alexander–Whitney product on the original
categorical Čech–de Rham total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Simplicial

universe u

variable (R : Type u) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R)))
  (N : SimplicialObject (FormalCoproduct.{u} X.left.Opens))

def bicomplex : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ) :=
  CechCoefficient.Total.bicomplex N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

def total : CochainComplex (ModuleCat.{u} R) ℕ := (bicomplex R X N).total (.up ℕ)

def signedPairing (p a q b : ℕ) :
    ((bicomplex R X N).X p).X a →ₗ[R] ((bicomplex R X N).X q).X b →ₗ[R]
      ((bicomplex R X N).X (p + q)).X (a + b) :=
  (-1 : ℤ) ^ (a * q) • CechCup.cup R X N p q a b

def totalCup (n m : ℕ) : (Cech.total R X N).X n →ₗ[R] (Cech.total R X N).X m →ₗ[R]
    (Cech.total R X N).X (n + m) :=
  BicomplexPairing.totalPairing (bicomplex R X N) (bicomplex R X N) (bicomplex R X N)
    (signedPairing R X N) n m

theorem totalCup_ι (n m p a q b : ℕ) (hpa : p + a = n) (hqb : q + b = m)
    (x : ((bicomplex R X N).X p).X a) (y : ((bicomplex R X N).X q).X b) :
    totalCup R X N n m ((bicomplex R X N).ιTotal (.up ℕ) p a n hpa x)
        ((bicomplex R X N).ιTotal (.up ℕ) q b m hqb y) =
      (-1 : ℤ) ^ (a * q) •
        (bicomplex R X N).ιTotal (.up ℕ) (p + q) (a + b) (n + m) (by
          change (p + q) + (a + b) = n + m
          omega) (CechCup.cup R X N p q a b x y) := by
  exact (BicomplexPairing.totalPairing_ι _ _ _ (signedPairing R X N)
    n m p a q b hpa hqb x y).trans (map_zsmul
      ((bicomplex R X N).ιTotal (.up ℕ) (p + q) (a + b) (n + m) (by
        change (p + q) + (a + b) = n + m
        omega)).hom ((-1 : ℤ) ^ (a * q)) (CechCup.cup R X N p q a b x y))

omit [Algebra ℚ R] in
theorem bicomplex_d_form_apply (p a : ℕ) (x : ((bicomplex R X N).X p).X a) :
    ((bicomplex R X N).d p (p + 1)).f a x = (CechDifferential.Cup.deRhamDifferential R X N p).app ⦋a⦌ x := by
  change (((FormalCoproduct.cochainComplexFunctor N).map
    ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X).d p (p + 1))).f a) x = _
  rw [show (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X).d p (p + 1) =
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R X p from CochainComplex.of_d _ _ p]
  rfl

omit [Algebra ℚ R] in
theorem bicomplex_d_cech_apply (p a : ℕ) (x : ((bicomplex R X N).X p).X a) :
    ((bicomplex R X N).X p).d a (a + 1) x =
      Cosimplicial.BilinearCup.differential (CechCup.cochains R X N p) a x :=
  Cosimplicial.BilinearCup.complex_d_apply (CechCup.cochains R X N p) a x

omit [Algebra ℚ R] in
theorem formDegreeCast_ι {p q a n : ℕ} (h : p = q) (hpa : p + a = n) (hqa : q + a = n)
    (x : ((bicomplex R X N).X p).X a) :
    (bicomplex R X N).ιTotal (.up ℕ) q a n hqa (CechDifferential.Cup.formDegreeCast R X N h ⦋a⦌ x) =
      (bicomplex R X N).ιTotal (.up ℕ) p a n hpa x := by
  subst q
  rfl

omit [Algebra ℚ R] in
theorem cechDegreeCast_ι {p a b n : ℕ} (h : a = b) (hpa : p + a = n) (hpb : p + b = n)
    (x : ((bicomplex R X N).X p).X a) :
    (bicomplex R X N).ιTotal (.up ℕ) p b n hpb
        (Cosimplicial.BilinearDegrees.Cup.degreeCast (CechCup.cochains R X N p) h x) =
      (bicomplex R X N).ιTotal (.up ℕ) p a n hpa x := by
  subst b
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.TotalCup.Cech

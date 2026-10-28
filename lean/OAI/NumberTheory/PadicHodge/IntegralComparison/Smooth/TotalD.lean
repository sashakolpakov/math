import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraicSmoothCechProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.ManifoldWedgeLeibniz

/-! # Total D -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.TotalD.AlgebraicCechProduct

noncomputable section

section

/-! The exterior derivative obeys the graded product rule on the
original smooth Čech cochains. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped Simplicial

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  (N : SimplicialObject (FormalCoproduct.{0} X.left.Opens))

def deRhamDifferential (p : ℕ) : AlgebraicSmoothCechProduct.smoothCochains X N p ⟶ AlgebraicSmoothCechProduct.smoothCochains X N (p + 1) :=
  (FormalCoproduct.cosimplicialObjectFunctor N).map
    ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).d p (p + 1))

theorem projection_deRhamDifferential (p : ℕ) (n : SimplexCategory) (i : (N.obj (op n)).I)
    (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj n) :
    Cech.BilinearPairing.projection N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X (p + 1)) n i
        ((deRhamDifferential X N p).app n x) =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d
        (Cech.BilinearPairing.projection N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p) n i x) := by
  have h := ConcreteCategory.congr_hom (Pi.map_π
    (fun j => ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).d p (p + 1)).app
      (op ((N.obj (op n)).obj j))) i) x
  change Cech.BilinearPairing.projection N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X (p + 1)) n i
      ((deRhamDifferential X N p).app n x) =
    ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).d p (p + 1)).app
      (op ((N.obj (op n)).obj i))
      (Cech.BilinearPairing.projection N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p) n i x) at h
  exact h.trans (by rw [AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex_d]; rfl)

def formDegreeCast {p q : ℕ} (h : p = q) (n : SimplexCategory) :
    (AlgebraicSmoothCechProduct.smoothCochains X N p).obj n ≃ₗ[ℂ] (AlgebraicSmoothCechProduct.smoothCochains X N q).obj n :=
  h ▸ LinearEquiv.refl ℂ ((AlgebraicSmoothCechProduct.smoothCochains X N p).obj n)

theorem projection_formDegreeCast {p q : ℕ} (h : p = q) (n : SimplexCategory)
    (i : (N.obj (op n)).I) (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj n) :
    Cech.BilinearPairing.projection N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X q) n i
        (formDegreeCast X N h n x) =
      ManifoldWedgeLeibniz.Smooth.openDegreeCast
        (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X ((N.obj (op n)).obj i)) h
        (Cech.BilinearPairing.projection N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p) n i x) := by
  subst q
  rfl

theorem pairing_natural (p q : ℕ) {n m : SimplexCategory} (f : n ⟶ m)
    (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj n) (y : (AlgebraicSmoothCechProduct.smoothCochains X N q).obj n) :
    (AlgebraicSmoothCechProduct.smoothCochains X N (p + q)).map f (AlgebraicSmoothCechProduct.pairing X N p q n x y) =
      AlgebraicSmoothCechProduct.pairing X N p q m ((AlgebraicSmoothCechProduct.smoothCochains X N p).map f x) ((AlgebraicSmoothCechProduct.smoothCochains X N q).map f y) :=
  Cech.BilinearPairing.pairing_natural N _ _ _ (AlgebraicSmoothPresheafProduct.pairing X p q)
    (AlgebraicSmoothPresheafProduct.pairing_natural X p q) f x y

theorem native_projection_pairing (p q : ℕ) (n : SimplexCategory)
    (i : (N.obj (op n)).I) (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj n) (y : (AlgebraicSmoothCechProduct.smoothCochains X N q).obj n) :
    Cech.BilinearPairing.projection N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X (p + q)) n i
        (AlgebraicSmoothCechProduct.pairing X N p q n x y) =
      AlgebraicSmoothPresheafProduct.pairing X p q (op ((N.obj (op n)).obj i))
        (Cech.BilinearPairing.projection N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p) n i x)
        (Cech.BilinearPairing.projection N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X q) n i y) :=
  Cech.BilinearPairing.projection_pairing N _ _ _
    (AlgebraicSmoothPresheafProduct.pairing X p q) n i x y

theorem native_projection_cast_pairing (p q t : ℕ) (h : p + q = t) (n : SimplexCategory)
    (i : (N.obj (op n)).I) (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj n) (y : (AlgebraicSmoothCechProduct.smoothCochains X N q).obj n) :
    Cech.BilinearPairing.projection N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X t) n i
        (formDegreeCast X N h n (AlgebraicSmoothCechProduct.pairing X N p q n x y)) =
      ManifoldWedgeLeibniz.Smooth.openDegreeCast
        (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X ((N.obj (op n)).obj i)) h
        (AlgebraicSmoothPresheafProduct.pairing X p q (op ((N.obj (op n)).obj i))
          (Cech.BilinearPairing.projection N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p) n i x)
          (Cech.BilinearPairing.projection N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X q) n i y)) :=
  (projection_formDegreeCast X N h n i _).trans
    (congrArg (ManifoldWedgeLeibniz.Smooth.openDegreeCast
      (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X ((N.obj (op n)).obj i)) h)
      (native_projection_pairing X N p q n i x y))

theorem deRhamDifferential_pairing (p q : ℕ) (n : SimplexCategory)
    (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj n) (y : (AlgebraicSmoothCechProduct.smoothCochains X N q).obj n) :
    (deRhamDifferential X N (p + q)).app n (AlgebraicSmoothCechProduct.pairing X N p q n x y) =
      formDegreeCast X N (by omega : (p + 1) + q = p + q + 1) n
        (AlgebraicSmoothCechProduct.pairing X N (p + 1) q n ((deRhamDifferential X N p).app n x) y) +
      (-1 : ℤ) ^ p • formDegreeCast X N (by omega : p + (q + 1) = p + q + 1) n
        (AlgebraicSmoothCechProduct.pairing X N p (q + 1) n x ((deRhamDifferential X N q).app n y)) := by
  apply Module.ProductScalarKernel.element_ext
    (fun i => ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X (p + q + 1)).obj
      (op ((N.obj (op n)).obj i)))
  intro i
  change Cech.BilinearPairing.projection N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X (p + q + 1)) n i _ =
    Cech.BilinearPairing.projection N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X (p + q + 1)) n i _
  let U := op ((N.obj (op n)).obj i)
  let px := Cech.BilinearPairing.projection N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X p) n i x
  let py := Cech.BilinearPairing.projection N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X q) n i y
  let pr := Cech.BilinearPairing.projection N ((AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X).X (p + q + 1)) n i
  let dx := (deRhamDifferential X N p).app n x
  let dy := (deRhamDifferential X N q).app n y
  let l := formDegreeCast X N (by omega : (p + 1) + q = p + q + 1) n
    (AlgebraicSmoothCechProduct.pairing X N (p + 1) q n dx y)
  let r := formDegreeCast X N (by omega : p + (q + 1) = p + q + 1) n
    (AlgebraicSmoothCechProduct.pairing X N p (q + 1) n x dy)
  have hl : pr l = ManifoldWedgeLeibniz.Smooth.openDegreeCast (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U.unop) (by omega)
      (AlgebraicSmoothPresheafProduct.pairing X (p + 1) q U
        (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d px) py) := by
    exact (native_projection_cast_pairing X N (p + 1) q (p + q + 1) (by omega) n i dx y).trans
      (congrArg (fun z => ManifoldWedgeLeibniz.Smooth.openDegreeCast
        (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U.unop) (by omega)
        (AlgebraicSmoothPresheafProduct.pairing X (p + 1) q U z py))
        (projection_deRhamDifferential X N p n i x))
  have hr : pr r = ManifoldWedgeLeibniz.Smooth.openDegreeCast (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U.unop) (by omega)
      (AlgebraicSmoothPresheafProduct.pairing X p (q + 1) U px
        (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d py)) := by
    exact (native_projection_cast_pairing X N p (q + 1) (p + q + 1) (by omega) n i x dy).trans
      (congrArg (fun z => ManifoldWedgeLeibniz.Smooth.openDegreeCast
        (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U.unop) (by omega)
        (AlgebraicSmoothPresheafProduct.pairing X p (q + 1) U px z))
        (projection_deRhamDifferential X N q n i y))
  have hleft := (projection_deRhamDifferential X N (p + q) n i (AlgebraicSmoothCechProduct.pairing X N p q n x y)).trans
    (congrArg Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (native_projection_pairing X N p q n i x y))
  have hproduct := ManifoldWedgeLeibniz.Smooth.open_d_wedge (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U.unop) px py
  have hsum : pr (l + (-1 : ℤ) ^ p • r) = pr l + (-1 : ℤ) ^ p • pr r :=
    (pr.map_add l _).trans (congrArg (pr l + ·) (map_zsmul pr ((-1 : ℤ) ^ p) r))
  exact hleft.trans (hproduct.trans
    ((congrArg₂ (fun (a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X)
        (AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U.unop) (p + q + 1)) => a + (-1 : ℤ) ^ p • b)
      hl hr).symm.trans hsum.symm))

theorem deRhamDifferential_cup (p q a b : ℕ)
    (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj ⦋a⦌) (y : (AlgebraicSmoothCechProduct.smoothCochains X N q).obj ⦋b⦌) :
    (deRhamDifferential X N (p + q)).app ⦋a + b⦌ (AlgebraicSmoothCechProduct.cup X N p q a b x y) =
      formDegreeCast X N (by omega : (p + 1) + q = p + q + 1) ⦋a + b⦌
        (AlgebraicSmoothCechProduct.cup X N (p + 1) q a b ((deRhamDifferential X N p).app ⦋a⦌ x) y) +
      (-1 : ℤ) ^ p • formDegreeCast X N (by omega : p + (q + 1) = p + q + 1) ⦋a + b⦌
        (AlgebraicSmoothCechProduct.cup X N p (q + 1) a b x ((deRhamDifferential X N q).app ⦋b⦌ y)) := by
  have hf := ConcreteCategory.congr_hom
    ((deRhamDifferential X N p).naturality (AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion a b)) x
  have hb := ConcreteCategory.congr_hom
    ((deRhamDifferential X N q).naturality (AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion a b)) y
  change (deRhamDifferential X N (p + q)).app ⦋a + b⦌
    (AlgebraicSmoothCechProduct.pairing X N p q ⦋a + b⦌ ((AlgebraicSmoothCechProduct.smoothCochains X N p).map (AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion a b) x)
      ((AlgebraicSmoothCechProduct.smoothCochains X N q).map (AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion a b) y)) = _
  rw [deRhamDifferential_pairing]
  change (deRhamDifferential X N p).app ⦋a + b⦌
    ((AlgebraicSmoothCechProduct.smoothCochains X N p).map (AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion a b) x) = _ at hf
  change (deRhamDifferential X N q).app ⦋a + b⦌
    ((AlgebraicSmoothCechProduct.smoothCochains X N q).map (AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion a b) y) = _ at hb
  rw [hf, hb]
  rfl

end

section

/-! Component formulas for the original smooth Čech total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Simplicial

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  (N : SimplicialObject (FormalCoproduct.{0} X.left.Opens))

theorem totalPairing_ι (n m p a q b : ℕ) (hpa : p + a = n) (hqb : q + b = m)
    (x : ((AlgebraicSmoothCechProduct.smoothBicomplex X N).X p).X a) (y : ((AlgebraicSmoothCechProduct.smoothBicomplex X N).X q).X b) :
    AlgebraicSmoothCechProduct.totalPairing X N n m ((AlgebraicSmoothCechProduct.smoothBicomplex X N).ιTotal (.up ℕ) p a n hpa x)
        ((AlgebraicSmoothCechProduct.smoothBicomplex X N).ιTotal (.up ℕ) q b m hqb y) =
      (-1 : ℤ) ^ (a * q) •
        (AlgebraicSmoothCechProduct.smoothBicomplex X N).ιTotal (.up ℕ) (p + q) (a + b) (n + m) (by
          change (p + q) + (a + b) = n + m
          omega) (AlgebraicSmoothCechProduct.cup X N p q a b x y) := by
  exact (BicomplexPairing.totalPairing_ι _ _ _ (AlgebraicSmoothCechProduct.signedPairing X N)
    n m p a q b hpa hqb x y).trans (map_zsmul
      ((AlgebraicSmoothCechProduct.smoothBicomplex X N).ιTotal (.up ℕ) (p + q) (a + b) (n + m) (by
        change (p + q) + (a + b) = n + m
        omega)).hom ((-1 : ℤ) ^ (a * q)) (AlgebraicSmoothCechProduct.cup X N p q a b x y))

theorem bicomplex_d_form_apply (p a : ℕ) (x : ((AlgebraicSmoothCechProduct.smoothBicomplex X N).X p).X a) :
    ((AlgebraicSmoothCechProduct.smoothBicomplex X N).d p (p + 1)).f a x = (deRhamDifferential X N p).app ⦋a⦌ x := rfl

theorem bicomplex_d_cech_apply (p a : ℕ) (x : ((AlgebraicSmoothCechProduct.smoothBicomplex X N).X p).X a) :
    ((AlgebraicSmoothCechProduct.smoothBicomplex X N).X p).d a (a + 1) x =
      Cosimplicial.BilinearCup.differential (AlgebraicSmoothCechProduct.smoothCochains X N p) a x :=
  Cosimplicial.BilinearCup.complex_d_apply (AlgebraicSmoothCechProduct.smoothCochains X N p) a x

def component (p a n : ℕ) (h : p + a = n) :
    (AlgebraicSmoothCechProduct.smoothCochains X N p).obj ⦋a⦌ →ₗ[ℂ] (AlgebraicSmoothCechProduct.smoothTotal X N).X n :=
  ((AlgebraicSmoothCechProduct.smoothBicomplex X N).ιTotal (.up ℕ) p a n h).hom

def totalDegreeCast {n m : ℕ} (h : n = m) : (AlgebraicSmoothCechProduct.smoothTotal X N).X n ≃ₗ[ℂ] (AlgebraicSmoothCechProduct.smoothTotal X N).X m :=
  h ▸ LinearEquiv.refl ℂ ((AlgebraicSmoothCechProduct.smoothTotal X N).X n)

def cupInto (n m k : ℕ) (h : n + m = k) :
    (AlgebraicSmoothCechProduct.smoothTotal X N).X n →ₗ[ℂ] (AlgebraicSmoothCechProduct.smoothTotal X N).X m →ₗ[ℂ] (AlgebraicSmoothCechProduct.smoothTotal X N).X k :=
  (AlgebraicSmoothCechProduct.totalPairing X N n m).compr₂ (totalDegreeCast X N h).toLinearMap

theorem cupInto_component (n m k p a q b : ℕ) (hnm : n + m = k)
    (hpa : p + a = n) (hqb : q + b = m)
    (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj ⦋a⦌) (y : (AlgebraicSmoothCechProduct.smoothCochains X N q).obj ⦋b⦌) :
    cupInto X N n m k hnm (component X N p a n hpa x) (component X N q b m hqb y) =
      (-1 : ℤ) ^ (a * q) • component X N (p + q) (a + b) k (by omega)
        (AlgebraicSmoothCechProduct.cup X N p q a b x y) := by
  subst k
  exact totalPairing_ι X N n m p a q b hpa hqb x y

theorem totalDegreeCast_component {p a n m : ℕ} (h : n = m) (hpa : p + a = n)
    (hpa' : p + a = m) (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj ⦋a⦌) :
    totalDegreeCast X N h (component X N p a n hpa x) = component X N p a m hpa' x := by
  subst m
  rfl

theorem component_formDegreeCast {p q a n : ℕ} (h : p = q) (hpa : p + a = n) (hqa : q + a = n)
    (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj ⦋a⦌) :
    component X N q a n hqa (formDegreeCast X N h ⦋a⦌ x) = component X N p a n hpa x := by
  subst q
  rfl

theorem component_cechDegreeCast {p a b n : ℕ} (h : a = b) (hpa : p + a = n) (hpb : p + b = n)
    (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj ⦋a⦌) :
    component X N p b n hpb (Cosimplicial.BilinearDegrees.Cup.degreeCast (AlgebraicSmoothCechProduct.smoothCochains X N p) h x) =
      component X N p a n hpa x := by
  subst b
  rfl

theorem differential_component (p a n : ℕ) (hpa : p + a = n) (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj ⦋a⦌) :
    (AlgebraicSmoothCechProduct.smoothTotal X N).d n (n + 1) (component X N p a n hpa x) =
      component X N (p + 1) a (n + 1) (by omega) ((deRhamDifferential X N p).app ⦋a⦌ x) +
      (-1 : ℤ) ^ p • component X N p (a + 1) (n + 1) (by omega)
        (Cosimplicial.BilinearCup.differential (AlgebraicSmoothCechProduct.smoothCochains X N p) a x) := by
  have h := ConcreteCategory.congr_hom (AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.ιTotal_d_of_sum (AlgebraicSmoothCechProduct.smoothBicomplex X N) p a n hpa) x
  simp only [Units.smul_def] at h
  change (AlgebraicSmoothCechProduct.smoothTotal X N).d n (n + 1) (component X N p a n hpa x) =
    component X N (p + 1) a (n + 1) (by omega) (((AlgebraicSmoothCechProduct.smoothBicomplex X N).d p (p + 1)).f a x) +
      (-1 : ℤ) ^ p • component X N p (a + 1) (n + 1) (by omega)
        (((AlgebraicSmoothCechProduct.smoothBicomplex X N).X p).d a (a + 1) x) at h
  exact h.trans (congrArg₂ (· + ·)
    (congrArg (component X N (p + 1) a (n + 1) (by omega))
      (bicomplex_d_form_apply X N p a x))
    (congrArg (fun z => (-1 : ℤ) ^ p • component X N p (a + 1) (n + 1) (by omega) z)
      (bicomplex_d_cech_apply X N p a x)))

end

/-! The two native differentials obey the product rule after inclusion into the smooth total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Simplicial

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  (N : SimplicialObject (FormalCoproduct.{0} X.left.Opens))

theorem component_deRhamDifferential_cup (p q a b k : ℕ) (hk : p + q + 1 + (a + b) = k)
    (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj ⦋a⦌) (y : (AlgebraicSmoothCechProduct.smoothCochains X N q).obj ⦋b⦌) :
    component X N (p + q + 1) (a + b) k hk
        ((deRhamDifferential X N (p + q)).app ⦋a + b⦌ (AlgebraicSmoothCechProduct.cup X N p q a b x y)) =
      component X N ((p + 1) + q) (a + b) k (by omega)
        (AlgebraicSmoothCechProduct.cup X N (p + 1) q a b ((deRhamDifferential X N p).app ⦋a⦌ x) y) +
      (-1 : ℤ) ^ p • component X N (p + (q + 1)) (a + b) k (by omega)
        (AlgebraicSmoothCechProduct.cup X N p (q + 1) a b x ((deRhamDifferential X N q).app ⦋b⦌ y)) := by
  rw [deRhamDifferential_cup]
  erw [map_add, map_zsmul, component_formDegreeCast, component_formDegreeCast]
  all_goals omega

theorem component_cechDifferential_cup (p q a b k : ℕ) (hk : (p + q) + (a + b + 1) = k)
    (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj ⦋a⦌) (y : (AlgebraicSmoothCechProduct.smoothCochains X N q).obj ⦋b⦌) :
    component X N (p + q) (a + b + 1) k hk
        (Cosimplicial.BilinearCup.differential (AlgebraicSmoothCechProduct.smoothCochains X N (p + q)) (a + b)
          (AlgebraicSmoothCechProduct.cup X N p q a b x y)) =
      component X N (p + q) ((a + 1) + b) k (by omega)
        (AlgebraicSmoothCechProduct.cup X N p q (a + 1) b
          (Cosimplicial.BilinearCup.differential (AlgebraicSmoothCechProduct.smoothCochains X N p) a x) y) +
      (-1 : ℤ) ^ a • component X N (p + q) (a + (b + 1)) k (by omega)
        (AlgebraicSmoothCechProduct.cup X N p q a (b + 1) x
          (Cosimplicial.BilinearCup.differential (AlgebraicSmoothCechProduct.smoothCochains X N q) b y)) := by
  have hc : Cosimplicial.BilinearCup.differential (AlgebraicSmoothCechProduct.smoothCochains X N (p + q)) (a + b)
      (AlgebraicSmoothCechProduct.cup X N p q a b x y) =
        Cosimplicial.BilinearDegrees.Cup.degreeCast (AlgebraicSmoothCechProduct.smoothCochains X N (p + q))
          (by omega : (a + 1) + b = a + b + 1)
          (AlgebraicSmoothCechProduct.cup X N p q (a + 1) b
            (Cosimplicial.BilinearCup.differential (AlgebraicSmoothCechProduct.smoothCochains X N p) a x) y) +
        (-1 : ℤ) ^ a • Cosimplicial.BilinearDegrees.Cup.degreeCast (AlgebraicSmoothCechProduct.smoothCochains X N (p + q))
          (by omega : a + (b + 1) = a + b + 1)
          (AlgebraicSmoothCechProduct.cup X N p q a (b + 1) x
            (Cosimplicial.BilinearCup.differential (AlgebraicSmoothCechProduct.smoothCochains X N q) b y)) :=
    Cosimplicial.BilinearDegrees.Cup.differential_cup_cast _ _ _ (AlgebraicSmoothCechProduct.pairing X N p q)
      (pairing_natural X N p q) a b x y
  rw [hc]
  erw [map_add, map_zsmul, component_cechDegreeCast, component_cechDegreeCast]
  all_goals omega

theorem differential_component_cup (p q a b k : ℕ) (hk : (p + q) + (a + b) = k)
    (x : (AlgebraicSmoothCechProduct.smoothCochains X N p).obj ⦋a⦌) (y : (AlgebraicSmoothCechProduct.smoothCochains X N q).obj ⦋b⦌) :
    (AlgebraicSmoothCechProduct.smoothTotal X N).d k (k + 1)
        (component X N (p + q) (a + b) k hk (AlgebraicSmoothCechProduct.cup X N p q a b x y)) =
      (component X N ((p + 1) + q) (a + b) (k + 1) (by omega)
          (AlgebraicSmoothCechProduct.cup X N (p + 1) q a b ((deRhamDifferential X N p).app ⦋a⦌ x) y) +
        (-1 : ℤ) ^ p • component X N (p + (q + 1)) (a + b) (k + 1) (by omega)
          (AlgebraicSmoothCechProduct.cup X N p (q + 1) a b x ((deRhamDifferential X N q).app ⦋b⦌ y))) +
      (-1 : ℤ) ^ (p + q) •
        (component X N (p + q) ((a + 1) + b) (k + 1) (by omega)
            (AlgebraicSmoothCechProduct.cup X N p q (a + 1) b
              (Cosimplicial.BilinearCup.differential (AlgebraicSmoothCechProduct.smoothCochains X N p) a x) y) +
          (-1 : ℤ) ^ a • component X N (p + q) (a + (b + 1)) (k + 1) (by omega)
            (AlgebraicSmoothCechProduct.cup X N p q a (b + 1) x
              (Cosimplicial.BilinearCup.differential (AlgebraicSmoothCechProduct.smoothCochains X N q) b y))) := by
  rw [differential_component, component_deRhamDifferential_cup, component_cechDifferential_cup]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.TotalD.AlgebraicCechProduct

import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CechCup

/-! # Cech Differential -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CechDifferential.Cup

noncomputable section

/-! The de Rham part of the differential obeys the graded product
rule on the original Čech cochains. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped Simplicial

universe u

variable (R : Type u) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R)))
  (N : SimplicialObject (FormalCoproduct.{u} X.left.Opens))

attribute [local instance] CechCup.rationalSections

def deRhamDifferential (p : ℕ) : CechCup.cochains R X N p ⟶ CechCup.cochains R X N (p + 1) :=
  (FormalCoproduct.cosimplicialObjectFunctor N).map (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R X p)

omit [Algebra ℚ R] in
theorem projection_deRhamDifferential (p : ℕ) (n : SimplexCategory) (i : (N.obj (op n)).I)
    (x : (CechCup.cochains R X N p).obj n) :
    Cech.BilinearPairing.projection N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X (p + 1)) n i
        ((deRhamDifferential R X N p).app n x) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R Γ(X.left, (N.obj (op n)).obj i) p
        (Cech.BilinearPairing.projection N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X p) n i x) := by
  exact ConcreteCategory.congr_hom (Pi.map_π
    (fun j => (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.differentialPresheaf R X p).app
      (op ((N.obj (op n)).obj j))) i) x

def formDegreeCast {p q : ℕ} (h : p = q) (n : SimplexCategory) :
    (CechCup.cochains R X N p).obj n ≃ₗ[R] (CechCup.cochains R X N q).obj n :=
  h ▸ LinearEquiv.refl R ((CechCup.cochains R X N p).obj n)

omit [Algebra ℚ R] in
theorem projection_formDegreeCast {p q : ℕ} (h : p = q) (n : SimplexCategory)
    (i : (N.obj (op n)).I) (x : (CechCup.cochains R X N p).obj n) :
    Cech.BilinearPairing.projection N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q) n i (formDegreeCast R X N h n x) =
      Wedge.degreeCast R Γ(X.left, (N.obj (op n)).obj i) h
        (Cech.BilinearPairing.projection N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X p) n i x) := by
  subst q
  rfl

theorem native_projection_pairing (p q : ℕ) (n : SimplexCategory)
    (i : (N.obj (op n)).I) (x : (CechCup.cochains R X N p).obj n) (y : (CechCup.cochains R X N q).obj n) :
    Cech.BilinearPairing.projection N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X (p + q)) n i (CechCup.pairing R X N p q n x y) =
      CechCup.sectionPairing R X p q (op ((N.obj (op n)).obj i))
        (Cech.BilinearPairing.projection N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X p) n i x)
        (Cech.BilinearPairing.projection N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q) n i y) :=
  Cech.BilinearPairing.projection_pairing N _ _ _ (CechCup.sectionPairing R X p q) n i x y

theorem native_projection_cast_pairing (p q t : ℕ) (h : p + q = t) (n : SimplexCategory)
    (i : (N.obj (op n)).I) (x : (CechCup.cochains R X N p).obj n) (y : (CechCup.cochains R X N q).obj n) :
    Cech.BilinearPairing.projection N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X t) n i
        (formDegreeCast R X N h n (CechCup.pairing R X N p q n x y)) =
      Wedge.degreeCast R Γ(X.left, (N.obj (op n)).obj i) h
        (CechCup.sectionPairing R X p q (op ((N.obj (op n)).obj i))
          (Cech.BilinearPairing.projection N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X p) n i x)
          (Cech.BilinearPairing.projection N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q) n i y)) :=
  (projection_formDegreeCast R X N h n i _).trans
    (congrArg (Wedge.degreeCast R Γ(X.left, (N.obj (op n)).obj i) h)
      (native_projection_pairing R X N p q n i x y))

theorem deRhamDifferential_pairing (p q : ℕ) (n : SimplexCategory)
    (x : (CechCup.cochains R X N p).obj n) (y : (CechCup.cochains R X N q).obj n) :
    (deRhamDifferential R X N (p + q)).app n (CechCup.pairing R X N p q n x y) =
      formDegreeCast R X N (by omega : (p + 1) + q = p + q + 1) n
        (CechCup.pairing R X N (p + 1) q n ((deRhamDifferential R X N p).app n x) y) +
      (-1 : ℤ) ^ p • formDegreeCast R X N (by omega : p + (q + 1) = p + q + 1) n
        (CechCup.pairing R X N p (q + 1) n x ((deRhamDifferential R X N q).app n y)) := by
  apply Module.ProductScalarKernel.element_ext
    (fun i => (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X (p + q + 1)).obj (op ((N.obj (op n)).obj i)))
  intro i
  let : Algebra R Γ(X.left, (N.obj (op n)).obj i) :=
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X ((N.obj (op n)).obj i)
  let : Algebra ℚ Γ(X.left, (N.obj (op n)).obj i) := CechCup.rationalSections R X ((N.obj (op n)).obj i)
  change Cech.BilinearPairing.projection N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X (p + q + 1)) n i _ =
    Cech.BilinearPairing.projection N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X (p + q + 1)) n i _
  let U := op ((N.obj (op n)).obj i)
  let : Algebra R Γ(X.left, U.unop) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U.unop
  let : Algebra ℚ Γ(X.left, U.unop) := CechCup.rationalSections R X U.unop
  let px := Cech.BilinearPairing.projection N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X p) n i x
  let py := Cech.BilinearPairing.projection N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q) n i y
  let pr := Cech.BilinearPairing.projection N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X (p + q + 1)) n i
  let dx := (deRhamDifferential R X N p).app n x
  let dy := (deRhamDifferential R X N q).app n y
  let l := formDegreeCast R X N (by omega : (p + 1) + q = p + q + 1) n
    (CechCup.pairing R X N (p + 1) q n dx y)
  let r := formDegreeCast R X N (by omega : p + (q + 1) = p + q + 1) n
    (CechCup.pairing R X N p (q + 1) n x dy)
  have hl : pr l = Wedge.degreeCast R Γ(X.left, U.unop) (by omega)
      (CechCup.sectionPairing R X (p + 1) q U
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R Γ(X.left, U.unop) p px) py) := by
    exact (native_projection_cast_pairing R X N (p + 1) q (p + q + 1) (by omega) n i dx y).trans
      (congrArg (fun z => Wedge.degreeCast R Γ(X.left, U.unop) (by omega)
        (CechCup.sectionPairing R X (p + 1) q U z py)) (projection_deRhamDifferential R X N p n i x))
  have hr : pr r = Wedge.degreeCast R Γ(X.left, U.unop) (by omega)
      (CechCup.sectionPairing R X p (q + 1) U px
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R Γ(X.left, U.unop) q py)) := by
    exact (native_projection_cast_pairing R X N p (q + 1) (p + q + 1) (by omega) n i x dy).trans
      (congrArg (fun z => Wedge.degreeCast R Γ(X.left, U.unop) (by omega)
        (CechCup.sectionPairing R X p (q + 1) U px z)) (projection_deRhamDifferential R X N q n i y))
  have hleft := (projection_deRhamDifferential R X N (p + q) n i (CechCup.pairing R X N p q n x y)).trans
    (congrArg (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R Γ(X.left, U.unop) (p + q))
      (native_projection_pairing R X N p q n i x y))
  have hproduct := @Leibniz.Wedge.differential_wedge R Γ(X.left, U.unop) _ _
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U.unop) (CechCup.rationalSections R X U.unop) p q px py
  have hsum : pr (l + (-1 : ℤ) ^ p • r) = pr l + (-1 : ℤ) ^ p • pr r :=
    (pr.map_add l _).trans (congrArg (pr l + ·) (map_zsmul pr ((-1 : ℤ) ^ p) r))
  exact hleft.trans (hproduct.trans
    ((congrArg₂ (fun (a b : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R Γ(X.left, U.unop) (p + q + 1)) =>
      a + (-1 : ℤ) ^ p • b) hl hr).symm.trans hsum.symm))

theorem deRhamDifferential_cup (p q a b : ℕ)
    (x : (CechCup.cochains R X N p).obj ⦋a⦌) (y : (CechCup.cochains R X N q).obj ⦋b⦌) :
    (deRhamDifferential R X N (p + q)).app ⦋a + b⦌ (CechCup.cup R X N p q a b x y) =
      formDegreeCast R X N (by omega : (p + 1) + q = p + q + 1) ⦋a + b⦌
        (CechCup.cup R X N (p + 1) q a b ((deRhamDifferential R X N p).app ⦋a⦌ x) y) +
      (-1 : ℤ) ^ p • formDegreeCast R X N (by omega : p + (q + 1) = p + q + 1) ⦋a + b⦌
        (CechCup.cup R X N p (q + 1) a b x ((deRhamDifferential R X N q).app ⦋b⦌ y)) := by
  have hf := ConcreteCategory.congr_hom
    ((deRhamDifferential R X N p).naturality (AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion a b)) x
  have hb := ConcreteCategory.congr_hom
    ((deRhamDifferential R X N q).naturality (AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion a b)) y
  change (deRhamDifferential R X N (p + q)).app ⦋a + b⦌
    (CechCup.pairing R X N p q ⦋a + b⦌ ((CechCup.cochains R X N p).map (AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion a b) x)
      ((CechCup.cochains R X N q).map (AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion a b) y)) = _
  rw [deRhamDifferential_pairing]
  change (deRhamDifferential R X N p).app ⦋a + b⦌
    ((CechCup.cochains R X N p).map (AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion a b) x) = _ at hf
  change (deRhamDifferential R X N q).app ⦋a + b⦌
    ((CechCup.cochains R X N q).map (AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion a b) y) = _ at hb
  rw [hf, hb]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CechDifferential.Cup

import OAI.AlgebraicGeometry.Betti.ProjectivePresentationCohomology
import OAI.AlgebraicTopology.Products.CupCohomology
import OAI.AlgebraicTopology.Kunneth.CanonicalCohomology
import OAI.AlgebraicTopology.Kunneth.CupPullbackSingular
import OAI.AlgebraicTopology.Kunneth.PresentationCupPurity
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-! # Add -/

namespace OAI.AlgebraicTopology.Kunneth.Add

noncomputable section

/-!
Proof development for Kunneth. The statement specification is kept in
`Statements/Kunneth.lean`; it is deliberately not imported here, since its
theorem is a proof placeholder. All declarations below use the actual
singular cohomology, pullbacks, and cup products.

This file proves the full original Kunneth statement: the canonical rational
Künneth decomposition and preservation of Hodge bidegrees. The latter uses
the actual differential-form wedge, simplex integration, and a proved
cochain homotopy to the original singular cup product.
-/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped DirectSum TensorProduct

namespace Construction

/-- The product universal property gives the expected bijection on points. -/
def productPointEquiv
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver)
    (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z.toOver ≃
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver × AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y.toOver where
  toFun z := (z ≫ πX, z ≫ πY)
  invFun xy := BinaryFan.IsLimit.lift hprod xy.1 xy.2
  left_inv z := by
    apply BinaryFan.IsLimit.hom_ext hprod
    · exact BinaryFan.IsLimit.lift_fst hprod _ _
    · exact BinaryFan.IsLimit.lift_snd hprod _ _
  right_inv xy := by
    apply Prod.ext
    · exact BinaryFan.IsLimit.lift_fst hprod _ _
    · exact BinaryFan.IsLimit.lift_snd hprod _ _

/-- The bijection is a homeomorphism, using projective compactness and
 Hausdorffness, with no extra topological assumptions. -/
def productPointHomeomorph
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver)
    (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z.toOver ≃ₜ
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver × AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y.toOver :=
  Continuous.homeoOfEquivCompactToT2 (f := productPointEquiv πX πY hprod)
    ((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map πX).prodMk
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map πY))

@[simp]
theorem productPointHomeomorph_apply
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver)
    (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY))
    (z : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z.toOver) :
    productPointHomeomorph πX πY hprod z =
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πX z, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πY z) := rfl

def productPointIso
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) :
    AlgebraicGeometry.Betti.Scheme.schemePointSpace Z.toOver ≅ TopCat.of (AlgebraicGeometry.Betti.Scheme.schemePointSpace X.toOver × AlgebraicGeometry.Betti.Scheme.schemePointSpace Y.toOver) :=
  TopCat.isoOfHomeo (productPointHomeomorph πX πY hprod)

@[reassoc (attr := simp)]
theorem productPointIso_fst
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) :
    (productPointIso πX πY hprod).hom ≫ TopCat.prodFst = AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map πX := by
  apply TopCat.ext
  intro z
  exact congrArg Prod.fst (productPointHomeomorph_apply πX πY hprod z)

@[reassoc (attr := simp)]
theorem productPointIso_snd
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) :
    (productPointIso πX πY hprod).hom ≫ TopCat.prodSnd = AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map πY := by
  apply TopCat.ext
  intro z
  exact congrArg Prod.snd (productPointHomeomorph_apply πX πY hprod z)

abbrev DegreePairs (n : ℕ) :=
  { ij : ℕ × ℕ // ij.1 + ij.2 = n }

abbrev KunnethSummand
    (X Y : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (ij : ℕ × ℕ) :=
  X.rationalCohomology ij.1 ⊗[ℚ] Y.rationalCohomology ij.2

abbrev KunnethSource
    (X Y : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :=
  ⨁ ij : DegreePairs n, KunnethSummand X Y ij.val

def exteriorProduct
    {R : Type} [CommRing R]
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver)
    (πY : Z.toOver ⟶ Y.toOver)
    (i j : ℕ)
    (a : AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of R R) X.toOver i)
    (b : AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of R R) Y.toOver j) :
    AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of R R) Z.toOver (i + j) :=
  Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace Z.toOver) i j
    (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of R R) i πX a)
    (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of R R) j πY b)

/-- The exterior product is bilinear over its coefficient ring. -/
def exteriorPairing
    {R : Type} [CommRing R]
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver)
    (πY : Z.toOver ⟶ Y.toOver)
    (i j : ℕ) :
    AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of R R) X.toOver i →ₗ[R]
      AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of R R) Y.toOver j →ₗ[R]
        AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of R R) Z.toOver (i + j) :=
  ((Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace Z.toOver) i j).compl₂
    (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of R R) j πY).hom).comp
      (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of R R) i πX).hom

@[simp]
theorem exteriorPairing_apply
    {R : Type} [CommRing R]
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver)
    (πY : Z.toOver ⟶ Y.toOver)
    (i j : ℕ)
    (a : AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of R R) X.toOver i)
    (b : AlgebraicGeometry.Betti.Scheme.schemeBetti (ModuleCat.of R R) Y.toOver j) :
    exteriorPairing πX πY i j a b = exteriorProduct πX πY i j a b := rfl

/-- Transport cohomology through an equality of degrees. -/
def rationalDegreeCast (Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    {m n : ℕ} (h : m = n) :
    Z.rationalCohomology m ≃ₗ[ℚ] Z.rationalCohomology n := by
  subst n
  exact LinearEquiv.refl ℚ _

@[simp]
theorem rationalDegreeCast_apply (Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    {m n : ℕ} (h : m = n) (a : Z.rationalCohomology m) :
    rationalDegreeCast Z h a =
      cast (congrArg (fun k => (Z.rationalCohomology k : Type)) h) a := by
  subst n
  rfl

/-- The canonical map on one tensor-product summand. -/
def kunnethComponent
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver)
    (πY : Z.toOver ⟶ Y.toOver)
    (n : ℕ) (ij : DegreePairs n) :
    KunnethSummand X Y ij.val →ₗ[ℚ] Z.rationalCohomology n :=
  (rationalDegreeCast Z ij.property).toLinearMap.comp
    (TensorProduct.lift (exteriorPairing πX πY ij.val.1 ij.val.2))

/-- The direct sum of the canonical exterior-product maps. -/
def kunnethMap
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver)
    (πY : Z.toOver ⟶ Y.toOver)
    (n : ℕ) : KunnethSource X Y n →ₗ[ℚ] Z.rationalCohomology n :=
  DirectSum.toModule ℚ (DegreePairs n) (Z.rationalCohomology n)
    (kunnethComponent πX πY n)

/-- The canonical map has exactly the normalization specified in Kunneth. -/
@[simp]
theorem kunnethMap_lof_tmul
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver)
    (πY : Z.toOver ⟶ Y.toOver)
    (n : ℕ) (ij : DegreePairs n)
    (a : X.rationalCohomology ij.val.1)
    (b : Y.rationalCohomology ij.val.2) :
    kunnethMap πX πY n
        (DirectSum.lof ℚ (DegreePairs n)
          (fun d => KunnethSummand X Y d.val) ij (a ⊗ₜ[ℚ] b)) =
      cast (congrArg (fun k => (Z.rationalCohomology k : Type)) ij.property)
        (exteriorProduct πX πY ij.val.1 ij.val.2 a b) := by
  simp [kunnethMap, kunnethComponent]

/-- Values on the exterior products determine a linear map uniquely. -/
theorem kunnethMap_unique
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver)
    (πY : Z.toOver ⟶ Y.toOver)
    (n : ℕ)
    (f : KunnethSource X Y n →ₗ[ℚ] Z.rationalCohomology n)
    (hf : ∀ (ij : DegreePairs n)
        (a : X.rationalCohomology ij.val.1)
        (b : Y.rationalCohomology ij.val.2),
      f (DirectSum.lof ℚ (DegreePairs n)
          (fun d => KunnethSummand X Y d.val) ij (a ⊗ₜ[ℚ] b)) =
        cast (congrArg (fun k => (Z.rationalCohomology k : Type)) ij.property)
          (exteriorProduct πX πY ij.val.1 ij.val.2 a b)) :
    f = kunnethMap πX πY n := by
  apply DirectSum.linearMap_ext
  intro ij
  apply TensorProduct.ext'
  intro a b
  exact (hf ij a b).trans (kunnethMap_lof_tmul πX πY n ij a b).symm

/-- The proved chain comparison and finite-dimensional duality give a
 linear decomposition on the actual projective product. -/
def kunnethLinearEquiv
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver)
    (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY))
    (n : ℕ) : KunnethSource X Y n ≃ₗ[ℚ] Z.rationalCohomology n := by
  let : ∀ m, FiniteDimensional ℚ
      ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (AlgebraicGeometry.Betti.Scheme.schemePointSpace X.toOver)).homology m) :=
    ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.projective_homology_finite X
  let : ∀ m, FiniteDimensional ℚ
      ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (AlgebraicGeometry.Betti.Scheme.schemePointSpace Y.toOver)).homology m) :=
    ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.projective_homology_finite Y
  exact (CanonicalCohomology.Construction.CanonicalCohomologyKunneth.canonicalCohomologyEquiv
    (AlgebraicGeometry.Betti.Scheme.schemePointSpace X.toOver) (AlgebraicGeometry.Betti.Scheme.schemePointSpace Y.toOver) n).trans
      (((Cohomology.Singular.Functor.singularCohomologyFunctor (ModuleCat.of ℚ ℚ) n).mapIso
        (productPointIso πX πY hprod).op).toLinearEquiv)

theorem productPullback_fst
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) (n : ℕ) (a : X.rationalCohomology n) :
    Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
      (productPointIso πX πY hprod).hom n
      (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (TopCat.prodFst (X := AlgebraicGeometry.Betti.Scheme.schemePointSpace X.toOver) (Y := AlgebraicGeometry.Betti.Scheme.schemePointSpace Y.toOver) :
          TopCat.of (AlgebraicGeometry.Betti.Scheme.schemePointSpace X.toOver × AlgebraicGeometry.Betti.Scheme.schemePointSpace Y.toOver) ⟶
          AlgebraicGeometry.Betti.Scheme.schemePointSpace X.toOver) n a) = AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n πX a :=
by
  have h := ConcreteCategory.congr_hom
    (Cohomology.Singular.Functor.singularCohomologyPullback_comp (ModuleCat.of ℚ ℚ)
      (productPointIso πX πY hprod).hom
      (TopCat.prodFst (X := AlgebraicGeometry.Betti.Scheme.schemePointSpace X.toOver) (Y := AlgebraicGeometry.Betti.Scheme.schemePointSpace Y.toOver)) n) a
  rw [productPointIso_fst] at h
  exact h.symm

theorem productPullback_snd
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) (n : ℕ) (b : Y.rationalCohomology n) :
    Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
      (productPointIso πX πY hprod).hom n
      (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (TopCat.prodSnd (X := AlgebraicGeometry.Betti.Scheme.schemePointSpace X.toOver) (Y := AlgebraicGeometry.Betti.Scheme.schemePointSpace Y.toOver) :
          TopCat.of (AlgebraicGeometry.Betti.Scheme.schemePointSpace X.toOver × AlgebraicGeometry.Betti.Scheme.schemePointSpace Y.toOver) ⟶
          AlgebraicGeometry.Betti.Scheme.schemePointSpace Y.toOver) n b) = AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n πY b :=
by
  have h := ConcreteCategory.congr_hom
    (Cohomology.Singular.Functor.singularCohomologyPullback_comp (ModuleCat.of ℚ ℚ)
      (productPointIso πX πY hprod).hom
      (TopCat.prodSnd (X := AlgebraicGeometry.Betti.Scheme.schemePointSpace X.toOver) (Y := AlgebraicGeometry.Betti.Scheme.schemePointSpace Y.toOver)) n) b
  rw [productPointIso_snd] at h
  exact h.symm

theorem kunnethLinearEquiv_lof_add
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) (p q : ℕ)
    (a : X.rationalCohomology p) (b : Y.rationalCohomology q) :
    kunnethLinearEquiv πX πY hprod (p + q)
      (DirectSum.lof ℚ (DegreePairs (p + q))
        (fun ij => KunnethSummand X Y ij.val) ⟨(p, q), rfl⟩ (a ⊗ₜ[ℚ] b)) =
      exteriorProduct πX πY p q a b := by
  let : ∀ m, FiniteDimensional ℚ
      ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (AlgebraicGeometry.Betti.Scheme.schemePointSpace X.toOver)).homology m) :=
    ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.projective_homology_finite X
  let : ∀ m, FiniteDimensional ℚ
      ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (AlgebraicGeometry.Betti.Scheme.schemePointSpace Y.toOver)).homology m) :=
    ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.projective_homology_finite Y
  change Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
    (productPointIso πX πY hprod).hom (p + q)
    (CanonicalCohomology.Construction.CanonicalCohomologyKunneth.canonicalCohomologyEquiv
      (AlgebraicGeometry.Betti.Scheme.schemePointSpace X.toOver) (AlgebraicGeometry.Betti.Scheme.schemePointSpace Y.toOver) (p + q)
      (DirectSum.lof ℚ (DegreePairs (p + q))
        (fun ij => KunnethSummand X Y ij.val) ⟨(p, q), rfl⟩ (a ⊗ₜ[ℚ] b))) = _
  erw [CanonicalCohomology.Construction.CanonicalCohomologyKunneth.canonicalCohomologyEquiv_lof_add
    (AlgebraicGeometry.Betti.Scheme.schemePointSpace X.toOver) (AlgebraicGeometry.Betti.Scheme.schemePointSpace Y.toOver) p q a b]
  erw [CupPullbackSingular.Construction.CupPullback.singularCohomologyCup_pullback
    (productPointIso πX πY hprod).hom p q]
  erw [productPullback_fst πX πY hprod p a, productPullback_snd πX πY hprod q b]
  rfl

theorem kunnethLinearEquiv_lof_tmul
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) (n : ℕ) (ij : DegreePairs n)
    (a : X.rationalCohomology ij.val.1) (b : Y.rationalCohomology ij.val.2) :
    kunnethLinearEquiv πX πY hprod n
      (DirectSum.lof ℚ (DegreePairs n) (fun d => KunnethSummand X Y d.val) ij (a ⊗ₜ[ℚ] b)) =
      cast (congrArg (fun m => (Z.rationalCohomology m : Type)) ij.property)
        (exteriorProduct πX πY ij.val.1 ij.val.2 a b) := by
  rcases ij with ⟨⟨p, q⟩, hpq⟩
  change p + q = n at hpq
  subst n
  exact kunnethLinearEquiv_lof_add πX πY hprod p q a b

theorem kunnethMap_bijective
    {X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) (n : ℕ) :
    Function.Bijective (kunnethMap πX πY n) := by
  have h := kunnethMap_unique πX πY n (kunnethLinearEquiv πX πY hprod n).toLinearMap
    (kunnethLinearEquiv_lof_tmul πX πY hprod n)
  rw [← h]
  exact (kunnethLinearEquiv πX πY hprod n).bijective

/-- The rational part of Kunneth, including its required exterior-product formula. -/
theorem kunneth_rational
    (X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) :
    ∃ e : ∀ n, KunnethSource X Y n ≃ₗ[ℚ] Z.rationalCohomology n,
      ∀ n ij (a : X.rationalCohomology ij.val.1) (b : Y.rationalCohomology ij.val.2),
        e n (DirectSum.lof ℚ (DegreePairs n) (fun d => KunnethSummand X Y d.val) ij (a ⊗ₜ[ℚ] b)) =
          cast (congrArg (fun m => (Z.rationalCohomology m : Type)) ij.property)
            (exteriorProduct πX πY ij.val.1 ij.val.2 a b) :=
  ⟨kunnethLinearEquiv πX πY hprod, kunnethLinearEquiv_lof_tmul πX πY hprod⟩

/-- Kunneth: exterior product gives the rational Künneth isomorphisms
 and preserves the induced Hodge bidegrees. -/
theorem kunneth_hodge
    (X Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (πX : Z.toOver ⟶ X.toOver)
    (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) :
    ∃ e : ∀ n : ℕ,
        KunnethSource X Y n ≃ₗ[ℚ] Z.rationalCohomology n,
      (∀ (n : ℕ) (ij : DegreePairs n)
          (a : X.rationalCohomology ij.val.1)
          (b : Y.rationalCohomology ij.val.2),
        e n
            (DirectSum.lof ℚ (DegreePairs n)
              (fun d => KunnethSummand X Y d.val) ij
              (a ⊗ₜ[ℚ] b)) =
          cast
            (congrArg (fun k => (Z.rationalCohomology k : Type))
              ij.property)
            (exteriorProduct (R := ℚ) πX πY
              ij.val.1 ij.val.2 a b)) ∧
      (∀ (p q r s : ℕ)
          (a : X.complexCohomology (p + q))
          (b : Y.complexCohomology (r + s)),
        a ∈ X.pureBettiSubspace p q →
        b ∈ Y.pureBettiSubspace r s →
        cast
            (congrArg (fun k => (Z.complexCohomology k : Type))
              (add_add_add_comm p q r s))
            (exteriorProduct (R := ℂ) πX πY
              (p + q) (r + s) a b) ∈
          Z.pureBettiSubspace (p + r) (q + s)) := by
  obtain ⟨e, he⟩ := kunneth_rational X Y Z πX πY hprod
  refine ⟨e, he, ?_⟩
  intro p q r s a b ha hb
  exact PresentationCupPurity.Constructions.presentationExteriorProduct_mem_pure X Y Z πX πY p q r s a b ha hb

end Construction

end

end OAI.AlgebraicTopology.Kunneth.Add

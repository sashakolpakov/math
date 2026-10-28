import OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperIntegral
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Extension.Presentation.Basic

/-! # Affine Compactification Of -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCompactificationOf.Construction.AffineCompactification

noncomputable section

/-! Explicit projective compactifications of finitely presented affine schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

structure Data {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) where
  n : ℕ
  scheme : Scheme.{u}
  base : scheme ⟶ Spec (.of R)
  proper : IsProper base
  chart : X ⟶ scheme
  openImmersion : IsOpenImmersion chart
  chart_base : chart ≫ base = f
  embedding : scheme ⟶ Proj (MvPolynomial.homogeneousSubmodule (Option (Fin n)) R)
  closedImmersion : IsClosedImmersion embedding
  embedding_base : embedding ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = base

def quotientEquiv {A : Type u} [CommRing A] [Algebra R A] {n m : ℕ}
    (P : Algebra.Presentation R A (Fin n) (Fin m)) :
    (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P.relation)) ≃ₐ[R] A := by
  rw [P.span_range_relation_eq_ker]
  exact P.quotientEquiv.restrictScalars R

def ofPresentation {A : Type u} [CommRing A] [Algebra R A] {n m : ℕ}
    (P : Algebra.Presentation R A (Fin n) (Fin m)) :
    Data (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  let d : Fin m → ℕ := fun i => (P.relation i).totalDegree
  let e := AffineCompactification.quotientEquiv P
  let j := Spec.map e.toRingEquiv.toCommRingCatIso.hom ≫
    SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogenizedChartOpen P.relation d (fun _ => le_rfl)
  have hj : IsOpenImmersion j := by
    have := SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogenizedChartOpen_isOpenImmersion P.relation d (fun _ => le_rfl)
    dsimp only [j]
    infer_instance
  refine ⟨n, SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogenizedProj P.relation d,
    SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogenizedProjπ P.relation d,
    SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogenizedProjπ_isProper P.relation d, j, hj, ?_,
    SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogenizedProjι P.relation d,
    SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogenizedProjι_isClosedImmersion P.relation d,
    SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogenizedProjι_comp_homogeneousProjπ P.relation d⟩
  dsimp only [j]
  rw [Category.assoc, SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogenizedChartOpen_comp_homogenizedProjπ,
    ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext e.toAlgHom.comp_algebraMap

def ofAlgebra (A : Type u) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] :
    Data (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  ofPresentation (Algebra.Presentation.ofFinitePresentation R A)

def ofAffine {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of R))
    [LocallyOfFinitePresentation f] : Data f := by
  let c := ProperIntegral.Construction.ProperIntegralFunctions.scalarMap f
  let : Algebra R Γ(X, ⊤) := c.hom.toAlgebra
  have hc : c.hom.FinitePresentation :=
    (RingHom.finitePresentation_respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (.of R)).inv f.appTop).mpr f.finitePresentation_appTop
  have : Algebra.FinitePresentation R Γ(X, ⊤) := hc
  let D := ofAlgebra (R := R) Γ(X, ⊤)
  have : IsOpenImmersion D.chart := D.openImmersion
  refine ⟨D.n, D.scheme, D.base, D.proper, X.isoSpec.hom ≫ D.chart,
    inferInstance, ?_, D.embedding, D.closedImmersion, D.embedding_base⟩
  rw [Category.assoc, D.chart_base]
  exact ProperIntegral.Construction.ProperIntegralFunctions.factor f

def ofFiniteType {X : Scheme.{u}} [IsAffine X] [IsNoetherianRing R]
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] : Data f :=
  ofAffine f

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCompactificationOf.Construction.AffineCompactification

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomogenizedProjectiveClosure
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Extension.Presentation.Basic

/-! # Compactification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Compactification.AffineCompactification

noncomputable section

/-! Explicit projective compactifications of finitely presented affine schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HomogenizedProjectiveClosure.PolynomialHomogenization

universe u

variable {R : Type u} [CommRing R]

structure Data {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) where
  coordinates : Type u
  finiteCoordinates : Finite coordinates
  scheme : Scheme.{u}
  base : scheme ⟶ Spec (.of R)
  proper : IsProper base
  chart : X ⟶ scheme
  openImmersion : IsOpenImmersion chart
  chart_base : chart ≫ base = f
  embedding : scheme ⟶ Proj (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (Option coordinates) R)
  closedImmersion : IsClosedImmersion embedding
  embedding_base : embedding ≫
    HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap
      (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (Option coordinates) R) = base

attribute [instance] Data.finiteCoordinates Data.proper Data.openImmersion Data.closedImmersion

def quotientEquiv {A σ : Type u} {κ : Type*} [CommRing A] [Algebra R A]
    (P : Algebra.Presentation R A σ κ) :
    (MvPolynomial σ R ⧸ Ideal.span (Set.range P.relation)) ≃ₐ[R] A := by
  rw [P.span_range_relation_eq_ker]
  exact P.quotientEquiv.restrictScalars R

def ofPresentation {A σ : Type u} {κ : Type*} [CommRing A] [Algebra R A] [Finite σ]
    (P : Algebra.Presentation R A σ κ) :
    Data (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  let d : κ → ℕ := fun i => (P.relation i).totalDegree
  let e := AffineCompactification.quotientEquiv P
  have : IsIso e.toRingEquiv.toCommRingCatIso.hom := e.toRingEquiv.toCommRingCatIso.isIso_hom
  let j := Spec.map e.toRingEquiv.toCommRingCatIso.hom ≫
    HomogenizedProjectiveClosure.PolynomialHomogenization.homogenizedAffineOpen P.relation d (fun _ => le_rfl)
  have hj : IsOpenImmersion j := by
    have := HomogenizedProjectiveClosure.PolynomialHomogenization.homogenizedAffineOpen_isOpenImmersion P.relation d (fun _ => le_rfl)
    dsimp only [j]
    infer_instance
  refine ⟨σ, inferInstance, HomogenizedProjectiveClosure.PolynomialHomogenization.homogenizedProjectiveClosure P.relation d,
    HomogenizedProjectiveClosure.PolynomialHomogenization.homogenizedProjectiveBase P.relation d,
    HomogenizedProjectiveClosure.PolynomialHomogenization.homogenizedProjectiveBase_proper P.relation d, j, hj, ?_,
    HomogenizedProjectiveClosure.PolynomialHomogenization.homogenizedProjectiveEmbedding P.relation d,
    HomogenizedProjectiveClosure.PolynomialHomogenization.homogenizedProjectiveEmbedding_closed P.relation d,
    HomogenizedProjectiveClosure.PolynomialHomogenization.homogenizedProjectiveEmbedding_over P.relation d⟩
  dsimp only [j]
  rw [Category.assoc, HomogenizedProjectiveClosure.PolynomialHomogenization.homogenizedAffineOpen_over, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext e.toAlgHom.comp_algebraMap

def ofAlgebra (A : Type u) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] :
    Data (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  ofPresentation ((Algebra.Presentation.ofFinitePresentation R A).reindex
    (Equiv.ulift : ULift.{u} _ ≃ _) (Equiv.refl _))

theorem coefficient_factor {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Coefficient.ModulePresheaf.schemeCoefficientMap f)) = f := by
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop) = f
  simp only [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

def ofAffine {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of R))
    [LocallyOfFinitePresentation f] : Data f := by
  let : Algebra R Γ(X, ⊤) := (Coefficient.ModulePresheaf.schemeCoefficientMap f).toAlgebra
  have hc : (Coefficient.ModulePresheaf.schemeCoefficientMap f).FinitePresentation :=
    (RingHom.finitePresentation_respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (.of R)).inv f.appTop).mpr f.finitePresentation_appTop
  have : Algebra.FinitePresentation R Γ(X, ⊤) := hc
  let D := ofAlgebra (R := R) Γ(X, ⊤)
  refine ⟨D.coordinates, D.finiteCoordinates, D.scheme, D.base, D.proper,
    X.isoSpec.hom ≫ D.chart, inferInstance, ?_,
    D.embedding, D.closedImmersion, D.embedding_base⟩
  rw [Category.assoc, D.chart_base]
  exact coefficient_factor f

def ofFiniteType {X : Scheme.{u}} [IsAffine X] [IsNoetherianRing R]
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] : Data f :=
  ofAffine f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Compactification.AffineCompactification

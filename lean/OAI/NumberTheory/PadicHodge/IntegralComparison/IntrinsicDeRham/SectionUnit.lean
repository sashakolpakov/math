import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenOrdinaryFormUnit

/-! # Section Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionUnit.Intrinsic

noncomputable section

/-! Native differential forms and the original sheaf de Rham complex
are canonically isomorphic on each affine étale coordinate chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

abbrev ring (U : X.left.Opens) : CommAlgCat.{u} R :=
  (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op U)

abbrev evaluation (U : X.left.Opens) :=
  sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R) ⋙
    (CategoryTheory.evaluation X.left.Opensᵒᵖ (ModuleCat.{u} R)).obj (op U)

def sections (U : X.left.Opens) : CochainComplex (ModuleCat.{u} R) ℕ :=
  ((Intrinsic.evaluation R X U).mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)

def rawIso (U : X.left.Opens) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R (ring R X U) ≅
    (((CategoryTheory.evaluation X.left.Opensᵒᵖ (ModuleCat.{u} R)).obj (op U)).mapHomologicalComplex
      (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro n m hnm
    change n + 1 = m at hnm
    subst m
    simp only [Functor.mapHomologicalComplex_obj_d, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex,
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex, CochainComplex.of_d, Iso.refl_hom]
    rfl)

def presheafUnit : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X ⟶
    ((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).mapHomologicalComplex
      (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) where
  f n := toSheafify (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)
  comm' n m _ := (toSheafify_naturality (Opens.grothendieckTopology X.left)
    ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X).d n m)).symm

def unit (U : X.left.Opens) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R (ring R X U) ⟶ sections R X U :=
  (rawIso R X U).hom ≫
    (((CategoryTheory.evaluation X.left.Opensᵒᵖ (ModuleCat.{u} R)).obj (op U)).mapHomologicalComplex
      (.up ℕ)).map (presheafUnit R X)

theorem unit_f (U : X.left.Opens) (n : ℕ) : (unit R X U).f n =
    (toSheafify (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)).app (op U) :=
  Category.id_comp _

variable (U : X.left.Opens) (hU : IsAffineOpen U)
  (σ : Type u) [LinearOrder σ] [Algebra (MvPolynomial σ R) (ring R X U)]
  [IsScalarTower R (MvPolynomial σ R) (ring R X U)]
  [Algebra.Etale (MvPolynomial σ R) (ring R X U)]

include hU σ in
theorem unit_isIso : IsIso (unit R X U) := by
  have (n : ℕ) : IsIso ((unit R X U).f n) := by
    rw [unit_f]
    exact AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenOrdinaryFormUnit.BaseAffineOpenOrdinaryFormUnit.forms R X U hU σ n
  exact HomologicalComplex.Hom.isIso_of_components _

def iso : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R (ring R X U) ≅ sections R X U := by
  let : IsIso (unit R X U) := unit_isIso R X U hU σ
  exact asIso (unit R X U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionUnit.Intrinsic

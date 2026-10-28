import OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedOrdinaryCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SectionCoordinatesRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.IntrinsicFormNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram

/-! # De Rham Section Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DeRhamSectionUnit

noncomputable section

/-! The original ordinary complex on all principal subopens of an affine
étale chart maps isomorphically to the actual sheaf de Rham sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (U : X.left.affineOpens)

abbrev Index := AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X.left, U.val)

def opens : Index R X U ⥤ X.left.Opens :=
  AffinePrincipal.Diagram.functor X.left U.val U.property ⋙ GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left

abbrev restriction := GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{u} R) (opens R X U)

def source : CochainComplex ((Index R X U)ᵒᵖ ⥤ ModuleCat.{u} R) ℕ :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IndexedOrdinaryCech.Ordinary.diagram R X (opens R X U))

def target : CochainComplex ((Index R X U)ᵒᵖ ⥤ ModuleCat.{u} R) ℕ :=
  ((restriction R X U).mapHomologicalComplex (.up ℕ)).obj
    (((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).mapHomologicalComplex
      (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X))

def map : source R X U ⟶ target R X U :=
  (IndexedOrdinaryCech.Ordinary.complexIso R X (opens R X U)).hom ≫
    ((restriction R X U).mapHomologicalComplex (.up ℕ)).map (IntrinsicDeRham.SectionUnit.Intrinsic.presheafUnit R X)

theorem component (q : ℕ) (r : Index R X U) :
    ((DeRhamSectionUnit.map R X U).f q).app (op r) =
      (IntrinsicDeRham.SectionUnit.Intrinsic.unit R X ((opens R X U).obj r)).f q := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  rfl

theorem integral_unit (q : ℕ) (r : Index R X U)
    (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X ((opens R X U).obj r)) q) :
    ((DeRhamSectionUnit.map R X U).f q).app (op r) ω =
      (Integral.IntrinsicFormNormalization.Intrinsic.iso R X ((opens R X U).obj r) q).hom
        (Integral.FormSectionUnit.unit R X q ((opens R X U).obj r) ω) := by
  rw [component]
  exact (Integral.IntrinsicFormNormalization.Intrinsic.unit R X ((opens R X U).obj r) q ω).symm

variable (σ : Type u) [LinearOrder σ]
  [Algebra (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U.val)]
  [IsScalarTower R (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U.val)]
  [Algebra.Etale (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U.val)]

include σ in
theorem map_isIso : IsIso (DeRhamSectionUnit.map R X U) := by
  have h (q : ℕ) (r : Index R X U) : IsIso (((DeRhamSectionUnit.map R X U).f q).app (op r)) := by
    let V := (AffinePrincipal.Diagram.functor X.left U.val U.property).obj r
    let i : V.val ⟶ U.val := homOfLE (X.left.basicOpen_le r.val)
    let := IntegralComparison.Etale.SectionCoordinatesRestriction.polynomialAlgebra R X i σ
    let := IntegralComparison.Etale.SectionCoordinatesRestriction.tower R X i σ
    let := IntegralComparison.Etale.SectionCoordinatesRestriction.etale R X i U.property V.property σ
    rw [component, IntrinsicDeRham.SectionUnit.Intrinsic.unit_f]
    exact AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenOrdinaryFormUnit.BaseAffineOpenOrdinaryFormUnit.forms R X V.val V.property σ q
  have hq (q : ℕ) : IsIso ((DeRhamSectionUnit.map R X U).f q) := by
    let hr (r : (Index R X U)ᵒᵖ) : IsIso (((DeRhamSectionUnit.map R X U).f q).app r) := h q r.unop
    exact NatIso.isIso_of_isIso_app _
  exact HomologicalComplex.Hom.isIso_of_components _

def iso : source R X U ≅ target R X U := by
  let := map_isIso R X U σ
  exact asIso (DeRhamSectionUnit.map R X U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DeRhamSectionUnit

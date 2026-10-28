import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.EtaleOrdinaryFormRegularity
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionBase
import OAI.NumberTheory.PadicHodge.GeometricComparison.OpenForms
import OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSheafOf

/-! # Open Form Regularity -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity

noncomputable section

/-! # Scalar regularity on the original sheaf sections of etale-coordinate affine opens -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (U : X.left.Opens) (hU : IsAffineOpen U)

abbrev ring : CommAlgCat.{u} R := (AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op U)

def chart : SectionTowers.BaseAffineSectionTowers.affineScheme R (ring R X U) ⟶ X :=
  Over.homMk hU.fromSpec (NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionBase.overBase R X U hU)

instance chart_open : IsOpenImmersion (chart R X U hU).left :=
  IsAffineOpen.isOpenImmersion_fromSpec hU

def sectionIso (n : ℕ) : ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n).obj.obj (op U) ≅
    ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R (SectionTowers.BaseAffineSectionTowers.affineScheme R (ring R X U))).X n).obj.obj (op ⊤) :=
  (NumberTheory.PadicHodge.GeometricComparison.OpenSheafOf.OpenSheafSections.iso R (chart R X U hU).left U
    ((Scheme.Hom.image_top_eq_opensRange _).trans hU.opensRange_fromSpec)
    ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n)).symm ≪≫
    (sheafToPresheaf (Opens.grothendieckTopology (Spec (CommRingCat.of (ring R X U)))) (ModuleCat.{u} R) ⋙
      (evaluation _ _).obj (op ⊤)).mapIso (NumberTheory.PadicHodge.GeometricComparison.OpenForms.OpenFormsSheaves.sheafIso (chart R X U hU) n)

variable (σ : Type u) [LinearOrder σ] [Algebra (MvPolynomial σ R) (ring R X U)]
  [IsScalarTower R (MvPolynomial σ R) (ring R X U)]
  [Algebra.Etale (MvPolynomial σ R) (ring R X U)]

include hU σ in
theorem regular (n : ℕ) (r : R) (hr : r ∈ nonZeroDivisors R) :
    IsSMulRegular (((DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n).obj.obj (op U)) r := by
  let e := (sectionIso R X U hU n).toLinearEquiv
  intro x y h
  apply e.injective
  apply Base.EtaleOrdinaryFormRegularity.BaseEtaleOrdinaryFormRegularity.global R (ring R X U) σ n r hr
  exact ((e.map_smul r x).symm.trans (congrArg e h)).trans (e.map_smul r y)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenFormRegularity.BaseAffineOpenFormRegularity

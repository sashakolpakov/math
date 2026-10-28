import OAI.NumberTheory.PadicHodge.IntegralComparison.StructuralQuotientDeRham
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham

/-! # Reduction Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.ReductionComplex

noncomputable section

/-! The original bounded crystalline Ext is computed by the coefficient quotient of the full smooth Witt de Rham complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k A σ : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [LinearOrder σ] [Fintype σ] [Algebra (MvPolynomial σ (WittVector p k)) A]
  [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A]
  [Algebra.Etale (MvPolynomial σ (WittVector p k)) A] (n : ℕ)

local notation "W" => WittVector p k
local notation "I" => (Ideal.span {(p : W)}) ^ (n + 1)
local notation "JA" => (Ideal.span {(p : A)}) ^ (n + 1)
local notation "An" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing.Ring p A n
local notation "CoeffW" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)

local instance frameAlgebra : Algebra W An := (FrameRing.base p k A n).toAlgebra

abbrev complex : CochainComplex (ModuleCat.{u} W) ℕ :=
  IntegralComparison.Module.IdealQuotient.complex W I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex W A)

def quotientIso : complex p k A n ≅ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex W An :=
  StructuralQuotientDeRham.iso W A σ I JA (FrameForms.powerIdeal_eq p k A n)
    (IntegralComparison.Etale.CoordinateFormBasis.coordinate W A σ) (IntegralComparison.Etale.CoordinateFormBasis.kaehlerBasis W A σ)
    (IntegralComparison.Etale.CoordinateFormBasis.kaehlerBasis_apply W A σ)

def reductionMap : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex W A ⟶ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex W An :=
  IntegralComparison.Module.IdealQuotient.complexProjection W I (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex W A) ≫
    (quotientIso p k A σ n).hom

omit [CharP k p] [Module.Flat (WittVector p k) A] [Fintype σ] in
theorem reductionMap_apply (m : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form W A m) :
    (reductionMap p k A σ n).f m ω = AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom
      (show A →ₐ[W] An from { toRingHom := Ideal.Quotient.mk JA, commutes' := fun _ => rfl })) m ω :=
  StructuralQuotientDeRham.projection_iso_apply W A σ I JA
    (FrameForms.powerIdeal_eq p k A n)
    (IntegralComparison.Etale.CoordinateFormBasis.coordinate W A σ) (IntegralComparison.Etale.CoordinateFormBasis.kaehlerBasis W A σ)
    (IntegralComparison.Etale.CoordinateFormBasis.kaehlerBasis_apply W A σ) m ω

abbrev coefficientComplex : CochainComplex (ModuleCat.{u + 2} CoeffW) ℕ :=
  ((DeRham.Comparison.coefficientFunctor p k).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (complex p k A n)

def coefficientIso : coefficientComplex p k A n ≅ DeRham.Comparison.deRhamComplex p k A n :=
  ((DeRham.Comparison.coefficientFunctor p k).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
    (quotientIso p k A σ n)

variable (C : Type u) [CommRing C] [Algebra k C] (ρ : A →+* C) (hρ : Function.Surjective ρ)
  (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w))

def homologyIso (i : ℕ) : (coefficientComplex p k A n).homology i ≅
    ModuleCat.of CoeffW (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n i) :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso (coefficientIso p k A σ n) ≪≫
    DeRham.Comparison.homologyIso p k A C σ ρ hρ hker hbase n i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.ReductionComplex

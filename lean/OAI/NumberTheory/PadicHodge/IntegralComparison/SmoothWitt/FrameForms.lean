import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseFormCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.FormFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis

/-! # Frame Forms -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameForms

noncomputable section

/-! Finite free original differential forms on the smooth Witt frames at every bounded level. -/

open OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing

universe u

variable (p : ℕ) [Fact p.Prime] (k A σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [LinearOrder σ] [Algebra (MvPolynomial σ (WittVector p k)) A]
  [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A]
  [Algebra.FormallyEtale (MvPolynomial σ (WittVector p k)) A] (n : ℕ)

local notation "W" => WittVector p k

local instance frameAlgebra : Algebra W (FrameRing.Ring p A n) := (FrameRing.base p k A n).toAlgebra

omit [Fintype k] [CharP k p] [Module.Flat (WittVector p k) A] in
theorem powerIdeal_eq : (Ideal.span {(p : A)}) ^ (n + 1) =
    ((Ideal.span {(p : W)}) ^ (n + 1)).map (algebraMap W A) := by
  rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]

def formsEquiv (m : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W (FrameRing.Ring p A n) (FrameRing.ideal p A n) (FrameRing.dividedPowers p k A n) m ≃ₗ[FrameRing.Ring p A n]
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form W (FrameRing.Ring p A n) m :=
  Principal.BaseFormCoordinates.formsEquiv W (FrameRing.Ring p A n) (p : W)
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (FrameRing.ideal p A n) (FrameRing.dividedPowers p k A n)
      (FrameComplex.ideal_eq p k A n) (FrameRing.base_isDPMorphism p k A n) m

omit [Fintype k] in
include σ in
theorem finite [Finite σ] (m : ℕ) :
    Module.Finite (FrameRing.Ring p A n) (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W (FrameRing.Ring p A n) (FrameRing.ideal p A n) (FrameRing.dividedPowers p k A n) m) := by
  let : Module.Finite (FrameRing.Ring p A n) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form W (FrameRing.Ring p A n) m) :=
    Quotient.FormFiniteness.structural_finite W A σ ((Ideal.span {(p : W)}) ^ (n + 1))
      ((Ideal.span {(p : A)}) ^ (n + 1)) (powerIdeal_eq p k A n)
      (Etale.CoordinateFormBasis.coordinate W A σ) (Etale.CoordinateFormBasis.kaehlerBasis W A σ)
      (Etale.CoordinateFormBasis.kaehlerBasis_apply W A σ) m
  exact Module.Finite.equiv (formsEquiv p k A n m).symm

omit [Fintype k] in
include σ in
theorem free (m : ℕ) :
    Module.Free (FrameRing.Ring p A n) (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W (FrameRing.Ring p A n) (FrameRing.ideal p A n) (FrameRing.dividedPowers p k A n) m) := by
  let : Module.Free (FrameRing.Ring p A n) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form W (FrameRing.Ring p A n) m) :=
    Quotient.FormFiniteness.structural_free W A σ ((Ideal.span {(p : W)}) ^ (n + 1))
      ((Ideal.span {(p : A)}) ^ (n + 1)) (powerIdeal_eq p k A n)
      (Etale.CoordinateFormBasis.coordinate W A σ) (Etale.CoordinateFormBasis.kaehlerBasis W A σ)
      (Etale.CoordinateFormBasis.kaehlerBasis_apply W A σ) m
  exact Module.Free.of_equiv (formsEquiv p k A n m).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameForms

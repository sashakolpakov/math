import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.StructuralFormBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameForms

/-! # Frame Form Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameFormBasis

noncomputable section

/-! Exact coordinate bases of the original bounded smooth Witt frame forms. -/

open OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing

universe u

variable (p : ℕ) [Fact p.Prime] (k A σ : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [LinearOrder σ] [Algebra (MvPolynomial σ (WittVector p k)) A]
  [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A]
  [Algebra.FormallyEtale (MvPolynomial σ (WittVector p k)) A] (n : ℕ)

local notation "W" => WittVector p k

local instance frameAlgebra : Algebra W (FrameRing.Ring p A n) := (FrameRing.base p k A n).toAlgebra

def ordinaryBasis (m : ℕ) : Module.Basis (Set.powersetCard σ m) (FrameRing.Ring p A n)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form W (FrameRing.Ring p A n) m) :=
  IntegralComparison.Quotient.StructuralFormBasis.basis W A σ ((Ideal.span {(p : W)}) ^ (n + 1))
    ((Ideal.span {(p : A)}) ^ (n + 1)) (FrameForms.powerIdeal_eq p k A n)
    (Etale.CoordinateFormBasis.coordinate W A σ) (Etale.CoordinateFormBasis.kaehlerBasis W A σ)
    (Etale.CoordinateFormBasis.kaehlerBasis_apply W A σ) m

def basis (m : ℕ) : Module.Basis (Set.powersetCard σ m) (FrameRing.Ring p A n)
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W (FrameRing.Ring p A n) (FrameRing.ideal p A n) (FrameRing.dividedPowers p k A n) m) :=
  (ordinaryBasis p k A σ n m).map (FrameForms.formsEquiv p k A n m).symm

theorem basis_apply (m : ℕ) (s : Set.powersetCard σ m) : basis p k A σ n m s =
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W (FrameRing.Ring p A n) (FrameRing.ideal p A n) (FrameRing.dividedPowers p k A n) 1
      (fun j => Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ (n + 1))
        (Etale.CoordinateFormBasis.coordinate W A σ (Set.powersetCard.ofFinEmbEquiv.symm s j))) := by
  apply (FrameForms.formsEquiv p k A n m).injective
  rw [basis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
  exact (IntegralComparison.Quotient.StructuralFormBasis.basis_apply W A σ ((Ideal.span {(p : W)}) ^ (n + 1))
    ((Ideal.span {(p : A)}) ^ (n + 1)) (FrameForms.powerIdeal_eq p k A n)
    (Etale.CoordinateFormBasis.coordinate W A σ) (Etale.CoordinateFormBasis.kaehlerBasis W A σ)
    (Etale.CoordinateFormBasis.kaehlerBasis_apply W A σ) m s).trans
      (Principal.BaseFormCoordinates.formsEquiv_symbol W (FrameRing.Ring p A n) (p : W)
        (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (FrameRing.ideal p A n) (FrameRing.dividedPowers p k A n)
        (FrameComplex.ideal_eq p k A n) (FrameRing.base_isDPMorphism p k A n) m 1 _).symm

variable (C : Type u) [CommRing C] [Algebra k C] (ρ : A →+* C)
  (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w))

def frameBasis (m : ℕ) :
    let F := WittFrame.object p k A C ρ hρ hker hbase n
    letI : Algebra W F.ring := F.base.toAlgebra
    Module.Basis (Set.powersetCard σ m) F.ring (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W F.ring F.ideal F.dividedPowers m) :=
  basis p k A σ n m

theorem frameBasis_apply (m : ℕ) (s : Set.powersetCard σ m) :
    let F := WittFrame.object p k A C ρ hρ hker hbase n
    letI : Algebra W F.ring := F.base.toAlgebra
    frameBasis p k A σ n C ρ hρ hker hbase m s = AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W F.ring F.ideal F.dividedPowers 1
      (fun j => Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ (n + 1))
        (Etale.CoordinateFormBasis.coordinate W A σ (Set.powersetCard.ofFinEmbEquiv.symm s j))) :=
  basis_apply p k A σ n m s

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameFormBasis

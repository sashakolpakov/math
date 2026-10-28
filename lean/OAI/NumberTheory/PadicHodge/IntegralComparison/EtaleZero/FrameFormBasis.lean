import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.DeRhamComplex

/-! # Frame Form Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameFormBasis

noncomputable section

/-!
# IntegralComparison: coordinate bases of the original Witt-relative étale zero-frame forms
-/

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [CommRing C] [Algebra k C]
  [Algebra (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) C]
  [Algebra.FormallyEtale (MvPolynomial σ k) C] [LinearOrder σ]

local notation "W" => WittVector p k

attribute [local instance] ZeroLevel.FormFiniteness.residueAlgebra
  ZeroLevel.FormFiniteness.ambientAlgebra ZeroLevel.FormFiniteness.coefficientTower

def coefficientEquiv (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W C ⊥ (dividedPowersBot C) n ≃ₗ[C]
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form k C n :=
  (PD.FormsBaseQuotientSymbols.formsEquiv W k C (WittVector.constantCoeff_surjective p)
    ⊥ (dividedPowersBot C) n).trans (AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.formsEquiv k C n)

theorem coefficientEquiv_symbol (n : ℕ) (a : C) (v : Fin n → C) :
    coefficientEquiv p k C n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W C ⊥ (dividedPowersBot C) a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol k C a v := by
  change AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.formsEquiv k C n
    (PD.FormsBaseQuotientSymbols.formsEquiv W k C (WittVector.constantCoeff_surjective p)
      ⊥ (dividedPowersBot C) n (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W C ⊥ (dividedPowersBot C) a v)) = _
  rw [PD.FormsBaseQuotientSymbols.formsEquiv_symbol, AlgebraicGeometry.Crystalline.Cohomology.ZeroIdeal.ZeroIdealPDForms.formsEquiv_symbol]

def basis (n : ℕ) : Module.Basis (Set.powersetCard σ n) C (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W C ⊥ (dividedPowersBot C) n) :=
  (Etale.CoordinateFormBasis.basis k C σ n).map (coefficientEquiv p k C n).symm

theorem basis_apply (n : ℕ) (s : Set.powersetCard σ n) : basis p k C σ n s =
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W C ⊥ (dividedPowersBot C) 1
      (fun j => Etale.CoordinateFormBasis.coordinate k C σ (Set.powersetCard.ofFinEmbEquiv.symm s j)) := by
  apply (coefficientEquiv p k C n).injective
  rw [basis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, coefficientEquiv_symbol]
  exact Etale.CoordinateFormBasis.basis_apply k C σ n s

variable [CharP k p]

def frameBasis (n : ℕ) :
    let U := ZeroLevel.LevelFrame.frame p k C
    letI : Algebra W U.ring := U.base.toAlgebra
    Module.Basis (Set.powersetCard σ n) U.ring (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W U.ring U.ideal U.dividedPowers n) :=
  basis p k C σ n

theorem frameBasis_apply (n : ℕ) (s : Set.powersetCard σ n) :
    let U := ZeroLevel.LevelFrame.frame p k C
    letI : Algebra W U.ring := U.base.toAlgebra
    frameBasis p k C σ n s = AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol W U.ring U.ideal U.dividedPowers 1
      (fun j => Etale.CoordinateFormBasis.coordinate k C σ (Set.powersetCard.ofFinEmbEquiv.symm s j)) :=
  basis_apply p k C σ n s

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameFormBasis

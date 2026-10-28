import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.DeRhamCoefficientComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.DeRham

/-! # Finite Model -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FiniteModel

noncomputable section

/-!
# IntegralComparison: original affine level-zero crystalline Ext has a finite Frobenius coordinate-module model
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable (p : ℕ) [Fact p.Prime] (k C : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C]

def model (i : ℕ) : ModuleCat.{u} C := (Frobenius.DeRhamComplex.complex k C).homology i

def coefficients (i : ℕ) : ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) :=
  (Global.DeRhamCoefficientComplex.coefficients p k).obj
    ((ModuleCat.restrictScalars (algebraMap k C)).obj (model k C i))

instance coefficients_preservesFiniteLimits :
    Limits.PreservesFiniteLimits (Global.DeRhamCoefficientComplex.coefficients p k) where
  preservesFiniteLimits T _ _ := by
    dsimp only [Global.DeRhamCoefficientComplex.coefficients, DeRham.Comparison.coefficientFunctor]
    infer_instance

instance coefficients_preservesFiniteColimits :
    Limits.PreservesFiniteColimits (Global.DeRhamCoefficientComplex.coefficients p k) where
  preservesFiniteColimits T _ _ := by
    dsimp only [Global.DeRhamCoefficientComplex.coefficients, DeRham.Comparison.coefficientFunctor]
    infer_instance

instance coefficients_preservesHomology :
    (Global.DeRhamCoefficientComplex.coefficients p k).PreservesHomology := by infer_instance

def deRhamIso (i : ℕ) : coefficients p k C i ≅
    (DeRham.Comparison.deRhamComplex p k C).homology i :=
  (Global.DeRhamCoefficientComplex.coefficients p k).mapIso (Frobenius.DeRhamComplex.homologyIso k C i) ≪≫
    (((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex k C).sc i).mapHomologyIso
      (Global.DeRhamCoefficientComplex.coefficients p k)).symm

variable (σ : Type u) [LinearOrder σ] [Fintype σ] [Algebra (MvPolynomial σ k) C]
  [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C]

omit [Fact p.Prime] [CharP k p] [LinearOrder σ] in
include σ in
theorem model_finite (i : ℕ) : Module.Finite C (model k C i) := by
  let : Algebra.FiniteType k C := Algebra.FiniteType.trans (S := MvPolynomial σ k) inferInstance inferInstance
  exact Frobenius.DeRhamFiniteness.homology_finite k C i

def homologyIso (i : ℕ) : coefficients p k C i ≅
    ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
        (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0 i) :=
  deRhamIso p k C i ≪≫ DeRham.Comparison.homologyIso p k C σ i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FiniteModel

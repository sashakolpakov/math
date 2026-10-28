import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Polynomial
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OperatorSpecialization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EquationValues
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Specialization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.DetectedPolynomial

/-! # Reference Polynomial Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferencePolynomialTransport.CM.Reference

noncomputable section

/-! Transport the original Albanese polynomial to the identical GeometricComparison
Hecke realization through the constructed arithmetic specialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM

variable {E K : Type} [Field E] [NumberField E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : PELModuli.CMPoints.Models.RankThreePELModel E K)
  {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)
  (R : M.GoodIntegralReduction q j)
  (a : M.Family) (hden : Nat.Coprime q M.arithmetic.denominator)
  (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence
    ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver))
  (χ : Fin M.s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])
  (hg : (Witt.PELSource.CM.heckeData M a C χ).HasIntegralModelGeometry)

local notation "D" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource.CM.heckeData M a C χ
local notation "A" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D hg j hden
local notation "G" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM.specialAlbanese R a
local notation "S" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM.sourceGroup D R.residue
local notation "op" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EquationValues.CM.Hecke.originalOperator M j R a hden C χ hg

theorem source_polynomial (H : Fin 3 → FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (G).X)
    (h : Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (G).X) H) :
    Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (S).X) H := h

theorem operator_eq (f : (D).EndK) :
    op f = Source.Specialization.CM.sourceSpecialization D hg j hden R.residue
      R.residue_compatibility (EndomorphismComparison.CM.integralEquiv (A).variety.scheme f) :=
  (EquationValues.CM.Hecke.originalOperator_eq M j R a hden C χ hg f).symm.trans
    (Intrinsic.OperatorSpecialization.CM.operator_eq D hg j hden R.residue
      R.residue_compatibility f)

theorem native_source_polynomial (f : Fin 3 → (D).EndK)
    (hpoly : Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (G).X) (fun i => op (f i))) :
    Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (S).X)
      (fun i => Intrinsic.EquationData.CM.IntrinsicPoints.operator D hg j hden R.residue
        R.residue_compatibility (f i)) :=
  Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.polynomial_congr q (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (S).X)
    (funext (fun i => (EquationValues.CM.Hecke.originalOperator_eq M j R a hden C χ hg (f i)).symm)) hpoly

variable {H : Type} [CommRing H] [Algebra ℚ H]

theorem specialized_polynomial (ρ : (A).HeckeRealization H) (h : Fin 3 → H)
    (f : Fin 3 → (D).EndK)
    (hf : ∀ i, ρ.action (h i) = (1 : ℚ) ⊗ₜ[ℤ] EndomorphismComparison.CM.integralEquiv (A).variety.scheme (f i))
    (hpoly : Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (G).X) (fun i => op (f i))) :
    Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q
      (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) (A).specialFiber.scheme)
      (fun i => Specialized.CM.Hecke.specializedHeckeAction A ρ (h i)) :=
  Intrinsic.Polynomial.CM.IntrinsicTransport.specialized_polynomial D hg j hden R.residue
    R.residue_compatibility ρ h f hf (native_source_polynomial M j R a hden C χ hg f hpoly)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferencePolynomialTransport.CM.Reference

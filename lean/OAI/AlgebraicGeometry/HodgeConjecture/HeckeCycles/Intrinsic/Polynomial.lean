import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OperatorSpecialization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.DetectedPolynomial

/-! # Polynomial -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Polynomial.CM.IntrinsicData

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalNeighbors.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.NeighborFormula.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator)
  (res : AbelianScheme.TateComparison.Data.modelRing K D.denominator →+* ZMod q)
  (hres : res.comp (algebraMap (NumberField.RingOfIntegers K)
    (AbelianScheme.TateComparison.Data.modelRing K D.denominator)) = j.residue)
  {L : Type} [Field L] [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L] [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L]
  [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L)

local notation "A" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D hg j hcop

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM
local notation "G" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM.sourceGroup D res
local notation "op" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EquationData.CM.IntrinsicPoints.operator D hg j hcop res hres

theorem operator_family_eq (f : Fin 3 → D.EndK) :
    (fun i => op (f i)) =
      (fun i => Source.Specialization.CM.sourceSpecialization D hg j hcop res hres
        (EndomorphismComparison.CM.integralEquiv (A).variety.scheme (f i))) :=
  funext (fun i => OperatorSpecialization.CM.operator_eq D hg j hcop res hres (f i))

theorem source_polynomial (f : Fin 3 → D.EndK)
    (hpoly : Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (G).X) (fun i => op (f i))) :
    Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (G).X)
      (fun i => Source.Specialization.CM.sourceSpecialization D hg j hcop res hres
        (EndomorphismComparison.CM.integralEquiv (A).variety.scheme (f i))) :=
  Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.polynomial_congr q (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (G).X)
    (operator_family_eq D hg j hcop res hres f) hpoly

variable {H : Type} [CommRing H] [Algebra ℚ H]

theorem compact_specialized_polynomial (ρ : (A).HeckeRealization H) (h : Fin 3 → H)
    (F : Fin 3 → FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (A).variety.scheme)
    (hF : ∀ i, ρ.action (h i) = (1 : ℚ) ⊗ₜ[ℤ] F i)
    (hp : Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (G).X)
      (fun i => Source.Specialization.CM.sourceSpecialization D hg j hcop res hres (F i))) :
    Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q
      (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) (A).specialFiber.scheme)
      (fun i => Specialized.CM.Hecke.specializedHeckeAction A ρ (h i)) :=
  Source.Specialization.CM.specializedHecke_polynomial D hg j hcop res hres ρ h F hF hp

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Polynomial.CM.IntrinsicData

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Polynomial.CM.IntrinsicIntegralOperators

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalNeighbors.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.NeighborFormula.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator)
  (res : AbelianScheme.TateComparison.Data.modelRing K D.denominator →+* ZMod q)
  (hres : res.comp (algebraMap (NumberField.RingOfIntegers K)
    (AbelianScheme.TateComparison.Data.modelRing K D.denominator)) = j.residue)
  {L : Type} [Field L] [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L] [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L]
  [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L)

local notation "A" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D hg j hcop

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM
local notation "G" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM.sourceGroup D res
local notation "op" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EquationData.CM.IntrinsicPoints.operator D hg j hcop res hres

def family (f : Fin 3 → D.EndK) : Fin 3 → FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (A).variety.scheme :=
  fun i => EndomorphismComparison.CM.integralEquiv (A).variety.scheme (f i)

theorem family_eq (f : Fin 3 → D.EndK) :
    family D hg j hcop f = (fun i => EndomorphismComparison.CM.integralEquiv (A).variety.scheme (f i)) := rfl

theorem family_at (f : Fin 3 → D.EndK) (i : Fin 3) :
    family D hg j hcop f i = EndomorphismComparison.CM.integralEquiv (A).variety.scheme (f i) :=
  congrFun (family_eq D hg j hcop f) i

theorem specialization_at (f : Fin 3 → D.EndK) (i : Fin 3) :
    Source.Specialization.CM.sourceSpecialization D hg j hcop res hres (family D hg j hcop f i) =
      op (f i) :=
  (congrArg (Source.Specialization.CM.sourceSpecialization D hg j hcop res hres)
    (family_at D hg j hcop f i)).trans
      (OperatorSpecialization.CM.operator_eq D hg j hcop res hres (f i)).symm

theorem specialization_family (f : Fin 3 → D.EndK) :
    (fun i => Source.Specialization.CM.sourceSpecialization D hg j hcop res hres
      (family D hg j hcop f i)) = (fun i => op (f i)) :=
  funext (specialization_at D hg j hcop res hres f)

theorem polynomial_for_family (f : Fin 3 → D.EndK)
    (hpoly : Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (G).X) (fun i => op (f i))) :
    Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (G).X)
      (fun i => Source.Specialization.CM.sourceSpecialization D hg j hcop res hres
        (family D hg j hcop f i)) :=
  Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.polynomial_congr q (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (G).X)
    (specialization_family D hg j hcop res hres f).symm hpoly

variable {H : Type} [CommRing H] [Algebra ℚ H]

theorem presentations (ρ : (A).HeckeRealization H) (h : Fin 3 → H)
    (f : Fin 3 → D.EndK)
    (hf : ∀ i, ρ.action (h i) = (1 : ℚ) ⊗ₜ[ℤ] EndomorphismComparison.CM.integralEquiv (A).variety.scheme (f i)) :
    ∀ i, ρ.action (h i) = (1 : ℚ) ⊗ₜ[ℤ] family D hg j hcop f i := by
  intro i
  exact (hf i).trans (congrArg (fun F : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (A).variety.scheme => (1 : ℚ) ⊗ₜ[ℤ] F)
    (family_at D hg j hcop f i).symm)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Polynomial.CM.IntrinsicIntegralOperators

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Polynomial.CM.IntrinsicTransport

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalNeighbors.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.NeighborFormula.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator)
  (res : AbelianScheme.TateComparison.Data.modelRing K D.denominator →+* ZMod q)
  (hres : res.comp (algebraMap (NumberField.RingOfIntegers K)
    (AbelianScheme.TateComparison.Data.modelRing K D.denominator)) = j.residue)
  {L : Type} [Field L] [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L] [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L]
  [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L)

local notation "A" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D hg j hcop

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM
local notation "G" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM.sourceGroup D res
local notation "op" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EquationData.CM.IntrinsicPoints.operator D hg j hcop res hres

variable {H : Type} [CommRing H] [Algebra ℚ H]
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Polynomial.CM.IntrinsicData

theorem specialized_polynomial (ρ : (A).HeckeRealization H) (h : Fin 3 → H)
    (f : Fin 3 → D.EndK)
    (hf : ∀ i, ρ.action (h i) = (1 : ℚ) ⊗ₜ[ℤ] EndomorphismComparison.CM.integralEquiv (A).variety.scheme (f i))
    (hpoly : Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q
      (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) (G).X) (fun i => op (f i))) :
    Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q
      (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) (A).specialFiber.scheme)
      (fun i => Specialized.CM.Hecke.specializedHeckeAction A ρ (h i)) :=
  IntrinsicData.compact_specialized_polynomial D hg j hcop res hres
    ρ h (IntrinsicIntegralOperators.family D hg j hcop f)
    (IntrinsicIntegralOperators.presentations D hg j hcop ρ h f hf)
    (IntrinsicIntegralOperators.polynomial_for_family D hg j hcop res hres f hpoly)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Polynomial.CM.IntrinsicTransport

end

end OAI

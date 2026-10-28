import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OperatorFamily
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MaskInsert
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TruncatedLower

/-! # Generator Family -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.GeneratorFamily.CM.Family

noncomputable section

/-! Upper and lower adelic quadratic generators are realized exactly
on each test function by finite products of actual local bare lifts. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OperatorFamily.CM.LocalFamily
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceAt.CM.Mask
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MaskInsert.CM
variable (n : ℕ)

local instance (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : MeasurableSpace ℚ_[OperatorFamily.CM.LocalFamily.number v] := borel ℚ_[OperatorFamily.CM.LocalFamily.number v]
local instance (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : BorelSpace ℚ_[OperatorFamily.CM.LocalFamily.number v] := ⟨rfl⟩

def upper (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) : OperatorFamily.CM.LocalFamily.Family n := fun v =>
  Schrodinger.CM.quadratic (OperatorFamily.CM.LocalFamily.number v) n
    ⟨B.map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection (OperatorFamily.CM.LocalFamily.number v)), hB.map _⟩

def lower (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) : OperatorFamily.CM.LocalFamily.Family n := fun v =>
  PrimeQuadratic.CM.Lower.conjugateQuadratic (OperatorFamily.CM.LocalFamily.number v) n
    ⟨B.map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection (OperatorFamily.CM.LocalFamily.number v)), hB.map _⟩

theorem upper_operator (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    OperatorFamily.CM.LocalFamily.operator n v (upper n B hB v) = Finite.Quadratic.CM.finiteQuadratic (Finite.PlaceAt.CM.Mask.matrixMask {v} B) := by
  have h := (PrimeQuadratic.CM.quadratic_operator (OperatorFamily.CM.LocalFamily.number v) n
    ⟨B.map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection (OperatorFamily.CM.LocalFamily.number v)), hB.map _⟩).symm
  rw [Finite.MaskInsert.CM.coefficients_projection, OperatorFamily.CM.LocalFamily.rationalPrime_number] at h
  exact h

theorem lower_operator (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    OperatorFamily.CM.LocalFamily.operator n v (lower n B hB v) = Finite.BareNe.CM.Group.bareAction
      (Finite.IntegralVacuum.CM.LowerBare.lowerLift (Finite.PlaceAt.CM.Mask.matrixMask {v} B) (Finite.PlaceAt.CM.Mask.matrixMask_symmetric _ B hB)) := by
  have h := (PrimeQuadratic.CM.Lower.lower_operator (OperatorFamily.CM.LocalFamily.number v) n
    ⟨B.map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection (OperatorFamily.CM.LocalFamily.number v)), hB.map _⟩).symm
  simp only [Finite.MaskInsert.CM.coefficients_projection, OperatorFamily.CM.LocalFamily.rationalPrime_number] at h
  exact h

theorem quadratic_zero : Finite.Quadratic.CM.finiteQuadratic (0 : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) = 1 := by
  apply LinearEquiv.ext
  intro f
  apply Subtype.ext
  funext x
  change Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic 0 x) * f.val x = f.val x
  simp [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic]

theorem lower_zero : Finite.BareNe.CM.Group.bareAction
    (Finite.IntegralVacuum.CM.LowerBare.lowerLift (0 : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) Matrix.isSymm_zero) = 1 := by
  change (Finite.FourierHeisenberg.CM.Equiv.fourierEquiv (I := Fin n))⁻¹ *
    Finite.Quadratic.CM.finiteQuadratic (-0) * Finite.FourierHeisenberg.CM.Equiv.fourierEquiv = 1
  rw [neg_zero, quadratic_zero, mul_one, inv_mul_cancel]

theorem product_upper (S : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    OperatorFamily.CM.LocalFamily.product n S (upper n B hB) = Finite.Quadratic.CM.finiteQuadratic (Finite.PlaceAt.CM.Mask.matrixMask (↑S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) B) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, Finite.MaskInsert.CM.matrixMask_empty, quadratic_zero]
    rfl
  | @insert v S hv ih =>
    change Finite.CommutingProduct.CM.product _ _ (insert v S) _ = _
    rw [Finite.CommutingProduct.CM.product_insert _ _ S v hv]
    change OperatorFamily.CM.LocalFamily.operator n v (upper n B hB v) * OperatorFamily.CM.LocalFamily.product n S (upper n B hB) = _
    rw [upper_operator, ih, ← Finite.PlaceAt.CM.QuadraticAddition.operator_add, ← Finite.MaskInsert.CM.matrixMask_insert S v hv]

theorem product_lower (S : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    OperatorFamily.CM.LocalFamily.product n S (lower n B hB) = Finite.BareNe.CM.Group.bareAction
      (Finite.IntegralVacuum.CM.LowerBare.lowerLift (Finite.PlaceAt.CM.Mask.matrixMask (↑S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) B)
        (Finite.PlaceAt.CM.Mask.matrixMask_symmetric _ B hB)) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.coe_empty, Finite.MaskInsert.CM.matrixMask_empty, lower_zero]
    rfl
  | @insert v S hv ih =>
    change Finite.CommutingProduct.CM.product _ _ (insert v S) _ = _
    rw [Finite.CommutingProduct.CM.product_insert _ _ S v hv]
    change OperatorFamily.CM.LocalFamily.operator n v (lower n B hB v) * OperatorFamily.CM.LocalFamily.product n S (lower n B hB) = _
    rw [lower_operator, ih, ← map_mul,
      ← Finite.PlaceAt.CM.QuadraticAddition.lowerLift_add _ _ (Finite.PlaceAt.CM.Mask.matrixMask_symmetric _ B hB) (Finite.PlaceAt.CM.Mask.matrixMask_symmetric _ B hB)]
    congr 2
    exact (Finite.MaskInsert.CM.matrixMask_insert S v hv B).symm

theorem upper_eventual (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :
    ∃ S : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, ∀ T : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, S ⊆ T →
      OperatorFamily.CM.LocalFamily.product n T (upper n B hB) f = Finite.Quadratic.CM.finiteQuadratic B f := by
  obtain ⟨S, hS⟩ := Finite.TruncatedLower.CM.Quadratic.exists_truncation B f
  exact ⟨S, fun T hT => by rw [product_upper]; exact hS T hT⟩

theorem lower_eventual (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :
    ∃ S : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, ∀ T : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, S ⊆ T →
      OperatorFamily.CM.LocalFamily.product n T (lower n B hB) f = Finite.BareNe.CM.Group.bareAction (Finite.IntegralVacuum.CM.LowerBare.lowerLift B hB) f := by
  obtain ⟨S, hS⟩ := Finite.TruncatedLower.CM.exists_truncation B hB f
  exact ⟨S, fun T hT => by rw [product_lower]; exact hS T hT⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.GeneratorFamily.CM.Family

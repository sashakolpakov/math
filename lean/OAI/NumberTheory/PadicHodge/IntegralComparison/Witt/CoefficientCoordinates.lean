import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Coefficient Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CoefficientCoordinates

noncomputable section

/-! Explicit additive coordinates for the native Witt coefficient
enlargement and its action on cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]

local notation "W" => WittVector p k
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham.Comparison.coefficientFunctor p k

instance preservesFiniteLimits : PreservesFiniteLimits F := by
  dsimp only [SmoothWitt.DeRham.Comparison.coefficientFunctor,
    Crystalline.RelativeResolution.coefficientFunctor]
  infer_instance

instance preservesFiniteColimits : PreservesFiniteColimits F := by
  dsimp only [SmoothWitt.DeRham.Comparison.coefficientFunctor,
    Crystalline.RelativeResolution.coefficientFunctor]
  infer_instance

instance preservesHomology : (F).PreservesHomology := by infer_instance

def addEquiv (M : ModuleCat.{u} W) : M ≃+ (F).obj M where
  toFun x := ULift.up (ULift.up x)
  invFun x := x.down.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem addEquiv_smul (M : ModuleCat.{u} W) (r : W) (x : M) :
    addEquiv p k M (r • x) = (ULift.up r : R) • addEquiv p k M x := rfl

theorem map_apply {M N : ModuleCat.{u} W} (f : M ⟶ N) (x : M) :
    (F).map f (addEquiv p k M x) = addEquiv p k N (f x) := rfl

def cohomologyEquiv (K : CochainComplex (ModuleCat.{u} W) ℕ) (i : ℕ) :
    (((F).mapHomologicalComplex (.up ℕ)).obj K).homology i ≃+ K.homology i :=
  (AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology.MappedComplexHomology.iso F K i).toLinearEquiv.toAddEquiv.trans
    (addEquiv p k (K.homology i)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CoefficientCoordinates

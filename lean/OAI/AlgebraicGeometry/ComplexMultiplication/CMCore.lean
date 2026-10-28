import OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety
import OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition
import OAI.AlgebraicGeometry.Betti.GeometricClasses
import OAI.AlgebraicTopology.DeRham.Comparison.RationalHodgeClasses
import Mathlib.RingTheory.TensorProduct.Basic

/-! # CM Core -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CMCore.CM

noncomputable section

/-!
# The CM manuscript's target in the project's actual cohomology

`cmHodgeClaim` below is a proposition, not a proved theorem. The required
geometric realization of the four-factor switch has not been supplied.

The CM condition is tied to the given variety's ordinary rational singular
cohomology. Its Hodge subspaces are obtained from the existing closed-form
subspaces by the canonical extension of the rational coefficient map.
No arbitrary comparison isomorphism or cycle-class surjectivity is assumed.
-/

open scoped TensorProduct

namespace AbelianVariety

local instance (A : CMAbelianVariety.CM.AbelianVariety) : Module ℚ (A.variety.complexCohomology 1) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (A : CMAbelianVariety.CM.AbelianVariety) :
    IsScalarTower ℚ ℂ (A.variety.complexCohomology 1) :=
  IsScalarTower.of_compHom ℚ ℂ _

/-- The actual map `z ⊗ a ↦ z • a_ℂ` from complexified rational singular cohomology. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1ScalarExtension (A : CMAbelianVariety.CM.AbelianVariety) :
    WeightOne.CM.Complexification (A.variety.rationalCohomology 1) →ₗ[ℂ]
      A.variety.complexCohomology 1 :=
  (A.variety.rationalCohomologyInclusion 1).hom.liftBaseChange ℂ

@[simp]
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1ScalarExtension_tmul (A : CMAbelianVariety.CM.AbelianVariety) (z : ℂ)
    (a : A.variety.rationalCohomology 1) :
    A.h1ScalarExtension (z ⊗ₜ[ℚ] a) =
      z • A.variety.rationalCohomologyInclusion 1 a := rfl

/-- Holomorphic type on the actual complexification of rational `H¹`. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Holomorphic (A : CMAbelianVariety.CM.AbelianVariety) :
    Submodule ℂ (WeightOne.CM.Complexification (A.variety.rationalCohomology 1)) :=
  (A.variety.pureBettiSubspace 1 0).comap A.h1ScalarExtension

/-- Antiholomorphic type on that same complexification. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Antiholomorphic (A : CMAbelianVariety.CM.AbelianVariety) :
    Submodule ℂ (WeightOne.CM.Complexification (A.variety.rationalCohomology 1)) :=
  (A.variety.pureBettiSubspace 0 1).comap A.h1ScalarExtension

/-- `H¹` admits the direct sum of rank-one CM Hodge structures specified in
the manuscript. The Hodge types are anchored to the variety's actual forms. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.HasCMH1 (A : CMAbelianVariety.CM.AbelianVariety) : Prop :=
  ∃ H : WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1),
    H.holomorphic = A.h1Holomorphic ∧
    H.antiholomorphic = A.h1Antiholomorphic ∧
    Nonempty (Decomposition.CM.CMDecomposition H)

/-- Compatibility with the two complementary Hodge types forces the actual
coefficient-extension map to be injective. The condition cannot be witnessed
by making that map vanish on an artificial tensor kernel. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.HasCMH1.h1ScalarExtension_injective {A : CMAbelianVariety.CM.AbelianVariety} (h : A.HasCMH1) :
    Function.Injective A.h1ScalarExtension := by
  obtain ⟨H, hh, ha, _⟩ := h
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  have hx0 : A.h1ScalarExtension x = 0 := hx
  have hxhol : x ∈ H.holomorphic := by
    rw [hh]
    change A.h1ScalarExtension x ∈ A.variety.pureBettiSubspace 1 0
    rw [hx0]
    exact Submodule.zero_mem _
  have hxanti : x ∈ H.antiholomorphic := by
    rw [ha]
    change A.h1ScalarExtension x ∈ A.variety.pureBettiSubspace 0 1
    rw [hx0]
    exact Submodule.zero_mem _
  have hxinf : x ∈ H.holomorphic ⊓ H.antiholomorphic := ⟨hxhol, hxanti⟩
  simpa only [H.complementary.inf_eq_bot] using hxinf

end AbelianVariety

/-- The full equality claimed in the manuscript, in every allowed codimension,
using the original project's geometric finite-rational-cycle image. -/
def cmHodgeClaim : Prop :=
  ∀ (A : CMAbelianVariety.CM.AbelianVariety), A.HasCMH1 →
    ∀ p : ℕ, p ≤ A.variety.complexDimension →
      A.variety.geometricAlgebraicClasses p = A.variety.rationalHodgeClasses p

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CMCore.CM

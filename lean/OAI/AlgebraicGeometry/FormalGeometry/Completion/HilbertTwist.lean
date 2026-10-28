import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso
import Mathlib.Algebra.Polynomial.Taylor

/-! # Hilbert Twist -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.HilbertTwist

noncomputable section

/-! Tensoring by the actual projective twist translates the canonical
Hilbert polynomial, including its lower coefficients. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory _root_.Polynomial

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

variable {K : Type u} [Field K] {r : ℕ}
  (M : (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)).Modules)
  (j : Fin (r + 1))

def projectiveTwist (n : ℕ) :
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)).Modules :=
  M ⊗ SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j n

instance projectiveTwist_quasicoherent [M.IsQuasicoherent] (n : ℕ) :
    (projectiveTwist M j n).IsQuasicoherent :=
  SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.moduleTensorCoordinateHyperplanePoleSheafPower_isQuasicoherent M j n

instance projectiveTwist_finiteType [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) :
    (projectiveTwist M j n).IsFiniteType :=
  SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.moduleTensorCoordinateHyperplanePoleSheafPower_isFiniteType M j n

def projectiveTwist_addIso (m n : ℕ) :
    projectiveTwist (projectiveTwist M j m) j n ≅ projectiveTwist M j (m + n) :=
  (α_ M (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j m)
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j n)) ≪≫
    (Iso.refl M ⊗ᵢ (SheafCohomology.Projective.TwistShiftIso.MvPolynomial.coordinateHyperplanePoleSheafPower_addIso j m n).symm)

theorem projectiveHilbertFunction_twist (m n : ℕ) :
    Projective.Numerics.Construction.projectiveHilbertFunction (projectiveTwist M j m) j n =
      Projective.Numerics.Construction.projectiveHilbertFunction M j (m + n) := by
  let G := SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor
    (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) (σ := Fin (r + 1)))
  exact congrArg (fun d : ℕ => (d : ℚ))
    (G.mapIso (projectiveTwist_addIso M j m n)).toLinearEquiv.finrank_eq

theorem projectiveHilbertPolynomial_twist [M.IsQuasicoherent] [M.IsFiniteType] (m : ℕ) :
    Projective.Numerics.Construction.projectiveHilbertPolynomial (projectiveTwist M j m) j =
      taylor (m : ℚ) (Projective.Numerics.Construction.projectiveHilbertPolynomial M j) := by
  obtain ⟨b, hb⟩ := Projective.Numerics.Construction.projectiveHilbertPolynomial_spec M j
  apply EventualPolynomial.Construction.eventualPolynomialValue_eq _ _ b
  intro n hn
  rw [projectiveHilbertFunction_twist, hb (m + n) (by omega), taylor_eval]
  simp only [Nat.cast_add, add_comm]

theorem projectiveHilbertPolynomial_twist_natDegree [M.IsQuasicoherent] [M.IsFiniteType]
    (m : ℕ) :
    (Projective.Numerics.Construction.projectiveHilbertPolynomial (projectiveTwist M j m) j).natDegree =
      (Projective.Numerics.Construction.projectiveHilbertPolynomial M j).natDegree := by
  rw [projectiveHilbertPolynomial_twist, natDegree_taylor]

theorem projectiveHilbertPolynomial_twist_leadingCoeff [M.IsQuasicoherent] [M.IsFiniteType]
    (m : ℕ) :
    (Projective.Numerics.Construction.projectiveHilbertPolynomial (projectiveTwist M j m) j).leadingCoeff =
      (Projective.Numerics.Construction.projectiveHilbertPolynomial M j).leadingCoeff := by
  rw [projectiveHilbertPolynomial_twist, leadingCoeff_taylor]

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.HilbertTwist

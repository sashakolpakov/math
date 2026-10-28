import OAI.AlgebraicGeometry.SheafCohomology.Projective.Euler
import OAI.AlgebraicGeometry.SheafCohomology.Projective.SectionsHilbertPolynomial
import OAI.AlgebraicGeometry.FormalGeometry.Completion.EventualPolynomial

/-! # Numerics -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics

noncomputable section

/-! Canonical Hilbert polynomials and additive Euler characteristics of
actual coherent modules on projective space over an arbitrary field. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {r : ℕ}

theorem fieldSpec_sections_isField : IsField Γ(Spec (CommRingCat.of K), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)

variable (M : (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)).Modules)
  (j : Fin (r + 1))

def projectiveHilbertFunction (n : ℕ) : ℚ :=
  (Module.finrank Γ(Spec (CommRingCat.of K), ⊤)
    ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) (σ := Fin (r + 1)))).obj
      ((SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := K) j n).functor.obj M)) : ℚ)

theorem projectiveHilbertFunction_eventuallyPolynomial [M.IsQuasicoherent] [M.IsFiniteType] :
    SheafCohomology.Projective.EventualPolynomial.EventuallyPolynomial (projectiveHilbertFunction M j) :=
  SheafCohomology.Projective.SectionsHilbertPolynomial.MvPolynomial.finiteType_projectiveTwist_sections_eventuallyPolynomial M j fieldSpec_sections_isField

def projectiveHilbertPolynomial [M.IsQuasicoherent] [M.IsFiniteType] : Polynomial ℚ :=
  EventualPolynomial.Construction.eventualPolynomialValue (projectiveHilbertFunction_eventuallyPolynomial M j)

theorem projectiveHilbertPolynomial_spec [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      projectiveHilbertFunction M j n = (projectiveHilbertPolynomial M j).eval (n : ℚ) :=
  EventualPolynomial.Construction.eventualPolynomialValue_spec (projectiveHilbertFunction_eventuallyPolynomial M j)

theorem projectiveHilbertFunction_iso
    {N : (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)).Modules}
    (e : M ≅ N) (n : ℕ) : projectiveHilbertFunction M j n = projectiveHilbertFunction N j n := by
  let F := SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) (σ := Fin (r + 1)))
  let T := (SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := K) j n).functor
  exact congrArg (fun d : ℕ => (d : ℚ)) (F.mapIso (T.mapIso e)).toLinearEquiv.finrank_eq

theorem projectiveHilbertPolynomial_iso [M.IsQuasicoherent] [M.IsFiniteType]
    {N : (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)).Modules}
    [N.IsQuasicoherent] [N.IsFiniteType] (e : M ≅ N) :
    projectiveHilbertPolynomial M j = projectiveHilbertPolynomial N j := by
  apply EventualPolynomial.Construction.eventualPolynomialValue_congr _ _ 0
  intro n _
  exact projectiveHilbertFunction_iso M j e n

theorem projectiveEuler_add_of_shortExact
    (T : ShortComplex (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)).Modules)
    (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent]
    [T.X₁.IsFiniteType] [T.X₂.IsFiniteType] [T.X₃.IsFiniteType] :
    SheafCohomology.Projective.Euler.MvPolynomial.projectiveSheafEuler T.X₂ =
      SheafCohomology.Projective.Euler.MvPolynomial.projectiveSheafEuler T.X₁ + SheafCohomology.Projective.Euler.MvPolynomial.projectiveSheafEuler T.X₃ :=
  SheafCohomology.Projective.Euler.MvPolynomial.projectiveSheafEuler_add_of_shortExact T hT fieldSpec_sections_isField

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics

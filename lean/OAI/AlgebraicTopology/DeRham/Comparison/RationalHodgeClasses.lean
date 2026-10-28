import OAI.AlgebraicTopology.DeRham.Comparison.Projective

/-! # Rational Hodge Classes -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RationalHodgeClasses.IntegralProjectiveVariety

noncomputable section

/-!
# The rational submodule of actual Hodge classes

The rational Hodge classes are the inverse image of the pure Betti subspace
under the actual rational-to-complex coefficient inclusion. The Betti
subspace uses the proved comparison from integration of genuine forms.

The containment criteria below take an arbitrary rational submodule. They
do not construct an algebraic cycle class map or state the Hodge conjecture.
-/

/-- Rational classes whose actual complex coefficient images have pure
type `(p,p)`, packaged as a rational submodule. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalHodgeClasses (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    Submodule ℚ (V.rationalCohomology (p + p)) := by
  letI : Module ℚ (V.complexCohomology (p + p)) :=
    Module.compHom _ (algebraMap ℚ ℂ)
  letI : IsScalarTower ℚ ℂ (V.complexCohomology (p + p)) :=
    IsScalarTower.of_compHom ℚ ℂ _
  exact ((V.pureBettiSubspace p p).restrictScalars ℚ).comap
    (V.rationalCohomologyInclusion (p + p)).hom

/-- This submodule has exactly the already defined actual Hodge classes
as its members. -/
@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.mem_rationalHodgeClasses (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (a : V.rationalCohomology (p + p)) :
    a ∈ V.rationalHodgeClasses p ↔ V.IsRationalHodgeClass p a :=
  Iff.rfl

/-- For any supplied rational submodule, universal membership of Hodge
classes is equivalent to containment of their actual submodule. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalHodgeClasses_le_iff (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (C : Submodule ℚ (V.rationalCohomology (p + p))) :
    V.rationalHodgeClasses p ≤ C ↔
      ∀ a, V.IsRationalHodgeClass p a → a ∈ C :=
  Iff.rfl

/-- Equivalently, each Hodge class is the image of an element of the
supplied submodule under its actual subtype inclusion. The submodule is
arbitrary; no claim that it is a cycle-class image is made here. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalHodgeClasses_le_iff_representable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (C : Submodule ℚ (V.rationalCohomology (p + p))) :
    V.rationalHodgeClasses p ≤ C ↔
      ∀ a, V.IsRationalHodgeClass p a →
        ∃ b : C, (b : V.rationalCohomology (p + p)) = a := by
  rw [V.rationalHodgeClasses_le_iff p C]
  constructor
  · intro h a ha
    exact ⟨⟨a, h a ha⟩, rfl⟩
  · intro h a ha
    obtain ⟨b, hb⟩ := h a ha
    exact hb ▸ b.property

/-- Failure of containment in an arbitrary supplied rational submodule
is witnessed by an actual rational Hodge class outside that submodule. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.exists_isRationalHodgeClass_not_mem_iff (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (C : Submodule ℚ (V.rationalCohomology (p + p))) :
    (∃ a, V.IsRationalHodgeClass p a ∧ a ∉ C) ↔
      ¬ V.rationalHodgeClasses p ≤ C := by
  classical
  rw [V.rationalHodgeClasses_le_iff p C]
  simp only [not_forall, exists_prop]

end

end OAI.AlgebraicTopology.DeRham.Comparison.RationalHodgeClasses.IntegralProjectiveVariety

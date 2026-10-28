import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricTorCoefficient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricSupportLocalization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Support

/-! # Total Tor Coefficient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TotalTorCoefficient

noncomputable section

/-! Native geometric Tor coefficients extend by zero off the
intersection, and agree at every local prime with the localized Euler coefficient. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

def coefficient (Z : Scheme) (A B : IrreducibleCloseds Z) (x : Z) (d : ℕ) : ℚ :=
  if h : x ∈ (A : Set Z) ∧ x ∈ (B : Set Z) then
    GeometricTorCoefficient.coefficient Z A B x h.1 h.2 d else 0

theorem localization (Z : Scheme) (A B : IrreducibleCloseds Z)
    (x : Z) (hxA : x ∈ (A : Set Z)) (hxB : x ∈ (B : Set Z))
    (p : PrimeSpectrum (Z.presheaf.stalk x)) (d : ℕ) :
    coefficient Z A B (Z.fromSpecStalk x p) d =
      ProjectionFormula.Tor.Euler.euler (Localization.AtPrime p.asIdeal)
        ((Flat.Extension.baseChange (Z.presheaf.stalk x) (Localization.AtPrime p.asIdeal)).obj
          (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA))
        ((Flat.Extension.baseChange (Z.presheaf.stalk x) (Localization.AtPrime p.asIdeal)).obj
          (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB)) d := by
  let R := Z.presheaf.stalk x
  let M := CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA
  let N := CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB
  by_cases hp : p ∈ Module.support R M ∩ Module.support R N
  · have hA := (GeometricSupportLocalization.mem_iff Z A x hxA p).mp hp.1
    have hB := (GeometricSupportLocalization.mem_iff Z B x hxB p).mp hp.2
    rw [coefficient, dite_eq_left ⟨hA, hB⟩]
    exact GeometricTorCoefficient.localization Z A B x hxA hxB p hp.1 hp.2 d
  · have hnot : ¬(Z.fromSpecStalk x p ∈ (A : Set Z) ∧ Z.fromSpecStalk x p ∈ (B : Set Z)) := by
      rintro ⟨hA, hB⟩
      exact hp ⟨(GeometricSupportLocalization.mem_iff Z A x hxA p).mpr hA,
        (GeometricSupportLocalization.mem_iff Z B x hxB p).mpr hB⟩
    rw [coefficient, dite_eq_right hnot, LocalizedTorEuler.euler]
    symm
    apply Finset.sum_eq_zero
    intro n _
    have hn : p ∉ Module.support R (((Tor (ModuleCat R) n).obj M).obj N) :=
      fun hn => hp (ProjectionFormula.Tor.Support.support_subset R M N n hn)
    rw [LocalizedTorEuler.length_zero R _ p hn]
    simp

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TotalTorCoefficient

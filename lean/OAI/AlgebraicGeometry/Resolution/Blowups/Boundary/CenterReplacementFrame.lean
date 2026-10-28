import OAI.AlgebraicGeometry.Resolution.Blowups.CenterGeneratorReplacement
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers

/-! # Center Replacement Frame -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CenterReplacementFrame.Construction

noncomputable section

/-! Dual center frames after replacing a generator by a smooth boundary equation. -/

universe u

variable {k R ι : Type u} [CommRing k] [CommRing R] [Algebra k R] [DecidableEq ι]

/-- A unit selected derivative supplies a dual frame for the exact
replacement family, by normalizing that derivative and correcting the
complementary derivatives only in its direction. -/
theorem exists_centerReplacement_dual_frame
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    (i : ι) (z : R) (hu : IsUnit (D i z)) :
    ∃ F : Option {j : ι // i ≠ j} → Derivation k R R,
      ∀ p q, F p (CenterGeneratorReplacement.Construction.centerReplacementFamily g i z q) = if p = q then 1 else 0 := by
  let u : Rˣ := hu.unit
  have huval : (u : R) = D i z := hu.unit_spec
  let E : Derivation k R R := (u⁻¹ : Rˣ) • D i
  let D' : {j : ι // i ≠ j} → Derivation k R R := fun j => D j.val
  let w : {j : ι // i ≠ j} → R := fun j => g j.val
  have hEz : E z = 1 := by
    change (u⁻¹ : Rˣ) • D i z = 1
    rw [← huval]
    exact Units.inv_mul u
  have hEw (j : {j : ι // i ≠ j}) : E (w j) = 0 := by
    change (u⁻¹ : Rˣ) • D i (g j.val) = 0
    rw [hD, ite_eq_right j.property, smul_zero]
  have hD' : ∀ p q, D' p (w q) = if p = q then 1 else 0 := by
    intro p q
    simpa only [Subtype.ext_iff] using hD p.val q.val
  exact ⟨AdaptedEtaleFrame.Construction.transverseExtendedDerivations D' E z, AdaptedEtaleFrame.Construction.transverseExtendedDerivations_dual D' w E z hD' hEz hEw⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CenterReplacementFrame.Construction

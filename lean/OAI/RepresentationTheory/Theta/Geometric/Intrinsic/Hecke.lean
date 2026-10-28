import OAI.RepresentationTheory.Theta.Geometric.DoubleCosets

/-! # Hecke -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Hecke

noncomputable section

def ActiveWeight := {a : Fin 3 → ℤ // Antitone a ∧ ∑ i, a i = 0}

def activeType {s : ℕ} (v : Fin s) (a : ActiveWeight) : AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType s where
  multiplier := 0
  exponent w i := if w = v then a.val i else 0
  dominant w := by
    by_cases h : w = v
    · simpa [h] using a.property.1
    · simp only [h, ite_false]
      exact fun _ _ _ => le_rfl

def clearingExponent {s : ℕ} (v : Fin s) (a : ActiveWeight) : ℕ :=
  Classical.choose (activeType v a).exists_integral_shift

def clearedActiveType {s : ℕ} (v : Fin s) (a : ActiveWeight) : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s :=
  ⟨(activeType v a).shift (clearingExponent v a),
    Classical.choose_spec (activeType v a).exists_integral_shift⟩

variable (q : ℕ) [Fact q.Prime]

private theorem product_unit_powers (a : ActiveWeight) :
    (∏ i : Fin 3, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ a.val i) = 1 := by
  have hp (t : Finset (Fin 3)) : (∏ i ∈ t, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ a.val i) =
      AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ (∑ i ∈ t, a.val i) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih => simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]
  simpa only [a.property.2, zpow_zero] using hp Finset.univ

def activeSLRepresentative (a : ActiveWeight) : SphericalGU.Spherical.SL3 q :=
  ⟨(AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.diagonalUnit (fun i => AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ a.val i)).val, by
    have h := congrArg Units.val (product_unit_powers q a)
    simpa only [AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.diagonalUnit, Matrix.det_diagonal, Units.coe_prod,
      Units.val_one] using h⟩

/-- Right cosets of the inverse representative encode the manuscript's
left-coset convention for inverse lattice branches. -/
abbrev activeCosets (a : ActiveWeight) :=
  DoubleCosets.Spherical.DoubleCosetFiber (SphericalGU.Spherical.integralSL3 q) (activeSLRepresentative q a)⁻¹

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Hecke

import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates

/-! # Padic Rational Lattice -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicRationalLattice.TestTransport

noncomputable section

/-! Rational scalars integral at q preserve every q-adic integer
lattice, including inverse level scalars at a good prime. -/

theorem padic_lattice_rational_smul (q : ℕ) [Fact q.Prime]
    {V : Type*} [AddCommGroup V] [Module (Padic q) V] [Module (PadicInt q) V]
    [Module ℚ V] [IsScalarTower (PadicInt q) (Padic q) V] [IsScalarTower ℚ (Padic q) V]
    (M : Submodule (PadicInt q) V) (r : ℚ) (hr : ‖(r : Padic q)‖ ≤ 1)
    (x : V) (hx : x ∈ M) : r • x ∈ M := by
  let z : PadicInt q := ⟨(r : Padic q), hr⟩
  have hz : algebraMap (PadicInt q) (Padic q) z = algebraMap ℚ (Padic q) r := rfl
  have he : z • x = r • x :=
    (IsScalarTower.algebraMap_smul (Padic q) z x).symm.trans
      ((congrArg (fun a : Padic q => a • x) hz).trans (IsScalarTower.algebraMap_smul (Padic q) r x))
  exact he ▸ M.smul_mem z hx

theorem padic_lattice_rational_division (q N : ℕ) [Fact q.Prime] (hcop : q.Coprime N)
    {V : Type*} [AddCommGroup V] [Module (Padic q) V] [Module (PadicInt q) V]
    [Module ℚ V] [IsScalarTower (PadicInt q) (Padic q) V] [IsScalarTower ℚ (Padic q) V]
    (M : Submodule (PadicInt q) V) (x y : V) (hx : x ∈ M) (hy : y ∈ M) :
    (N : ℚ)⁻¹ • (x - y) ∈ M := by
  apply padic_lattice_rational_smul q M _ _ _ (M.sub_mem hx hy)
  simp only [Rat.cast_inv, Rat.cast_natCast, norm_inv, Padic.norm_natCast_eq_one_iff.mpr hcop, inv_one,
    le_refl]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicRationalLattice.TestTransport

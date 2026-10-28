import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Basis
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SuperlatticeType

/-! # Superlattice -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Superlattice.Construction

noncomputable section

/-!
The additive quotient of a bounded q-adic superlattice is the elementary
module attached to its dominant exponents. The basis is constructed in
the actual superlattice, and the smaller lattice is its diagonal span.
-/

open _root_.Module

open OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction

variable (q : ℕ) [Fact q.Prime] {d : ℕ}

def superlatticeBasis
    (M : Submodule ℤ_[q] (Fin d → ℚ_[q]))
    (e : Basis (Fin d) ℚ_[q] (Fin d → ℚ_[q])) (a : Fin d → ℕ)
    (heM : M = LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e (fun i => -(a i : ℤ))) :
    Basis (Fin d) ℤ_[q] M :=
  ((Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.powerBasis (q : ℤ_[q]) PadicInt.irreducible_p e
    (fun i => -(a i : ℤ))).restrictScalars ℤ_[q]).map
    (LinearEquiv.ofEq _ M
      (heM.trans (LatticeBounds.Construction.diagonalLattice_eq_powerBasis_span _ PadicInt.irreducible_p _ _)).symm)

theorem superlatticeBasis_coe
    (M : Submodule ℤ_[q] (Fin d → ℚ_[q]))
    (e : Basis (Fin d) ℚ_[q] (Fin d → ℚ_[q])) (a : Fin d → ℕ)
    (heM : M = LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e (fun i => -(a i : ℤ))) (i : Fin d) :
    ((superlatticeBasis q M e a heM i : M) : Fin d → ℚ_[q]) =
      (q : ℚ_[q]) ^ (-(a i : ℤ)) • e i := by
  simp only [superlatticeBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Basis.restrictScalars_apply, Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.powerBasis_apply, map_natCast]

theorem superlatticeBasis_scaled_coe
    (M : Submodule ℤ_[q] (Fin d → ℚ_[q]))
    (e : Basis (Fin d) ℚ_[q] (Fin d → ℚ_[q])) (a : Fin d → ℕ)
    (heM : M = LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e (fun i => -(a i : ℤ))) (i : Fin d) :
    (((q : ℤ_[q]) ^ a i • superlatticeBasis q M e a heM i : M) : Fin d → ℚ_[q]) =
      e i := by
  have hq : (q : ℚ_[q]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  change (q : ℤ_[q]) ^ a i •
    ((superlatticeBasis q M e a heM i : M) : Fin d → ℚ_[q]) = _
  rw [superlatticeBasis_coe, ← algebraMap_smul ℚ_[q], map_pow, map_natCast,
    smul_smul, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ hq), one_smul]

theorem superlattice_comap_eq_diagonal
    (L M : Submodule ℤ_[q] (Fin d → ℚ_[q])) (hlower : L ≤ M)
    (e : Basis (Fin d) ℚ_[q] (Fin d → ℚ_[q])) (a : Fin d → ℕ)
    (heL : L = Submodule.span ℤ_[q] (Set.range e))
    (heM : M = LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e (fun i => -(a i : ℤ))) :
    L.comap M.subtype = IsogenyQuotient.Basis.Construction.basisDiagonalSubmodule q (superlatticeBasis q M e a heM) a := by
  apply Submodule.map_injective_of_injective M.injective_subtype
  rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr hlower]
  rw [IsogenyQuotient.Basis.Construction.basisDiagonalSubmodule, Submodule.map_span, ← Set.range_comp]
  have hgen : (M.subtype ∘ fun i =>
      (q : ℤ_[q]) ^ a i • superlatticeBasis q M e a heM i) = e := by
    funext i
    exact superlatticeBasis_scaled_coe q M e a heM i
  rw [hgen, heL]

/-- The quotient of the actual superlattice by the smaller lattice,
with no auxiliary group-type premise. -/
def superlatticeQuotientEquiv
    (L M : Submodule ℤ_[q] (Fin d → ℚ_[q])) (hlower : L ≤ M)
    (e : Basis (Fin d) ℚ_[q] (Fin d → ℚ_[q])) (a : Fin d → ℕ)
    (heL : L = Submodule.span ℤ_[q] (Set.range e))
    (heM : M = LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e (fun i => -(a i : ℤ))) :
    M ⧸ (L.comap M.subtype).toAddSubgroup ≃+ (∀ i, ZMod (q ^ a i)) :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (congrArg Submodule.toAddSubgroup
      (superlattice_comap_eq_diagonal q L M hlower e a heL heM))).trans
    (IsogenyQuotient.Basis.Construction.basisDiagonalQuotientEquiv q (superlatticeBasis q M e a heM) a)

theorem bounded_superlattice_quotient_type_from_ElementaryDivisors
    (L M : Submodule ℤ_[q] (Fin d → ℚ_[q]))
    [Submodule.IsLattice ℚ_[q] L] [Submodule.IsLattice ℚ_[q] M]
    (h : ℕ) (hlower : L ≤ M)
    (hupper : M ≤ SuperlatticeType.Construction.uniformizerPowerLattice (q : ℤ_[q]) PadicInt.irreducible_p (-(h : ℤ)) L)
    (h_ElementaryDivisors : ElementaryDivisors.Construction.ElementaryDivisorsInput.{0}) :
    ∃! a : Fin d → ℕ,
      Antitone a ∧ (∀ i, a i ≤ h) ∧
      (∃ e : Basis (Fin d) ℚ_[q] (Fin d → ℚ_[q]),
        L = Submodule.span ℤ_[q] (Set.range e) ∧
        M = LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e (fun i => -(a i : ℤ))) ∧
      Nonempty (M ⧸ (L.comap M.subtype).toAddSubgroup ≃+ (∀ i, ZMod (q ^ a i))) := by
  obtain ⟨a, ⟨ha, hab, e, heL, heM⟩, hu⟩ :=
    SuperlatticeType.Construction.bounded_superlattice_type_from_ElementaryDivisors (q : ℤ_[q]) PadicInt.irreducible_p
      L M h hlower hupper h_ElementaryDivisors
  refine ⟨a, ⟨ha, hab, ⟨e, heL, heM⟩,
    ⟨superlatticeQuotientEquiv q L M hlower e a heL heM⟩⟩, ?_⟩
  rintro a' ⟨ha', hab', he', _⟩
  exact hu a' ⟨ha', hab', he'⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Superlattice.Construction

import OAI.AlgebraicTopology.Cohomology.Singular.Representatives

/-! # Chain Representatives -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives

noncomputable section

/-!
# Representatives for the homology paired with singular cohomology

These are the chain-complex counterparts of the cocycle representatives.
They use mathlib's existing explicit kernel/image description of homology.
-/

open _root_.CategoryTheory

variable {R : Type} [Ring R]

abbrev chainCycles (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Submodule R (C.X n) :=
  LinearMap.ker (C.sc n).g.hom

abbrev chainBoundaryMap (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    (C.sc n).X₁ →ₗ[R] chainCycles C n :=
  (C.sc n).moduleCatToCycles

abbrev chainBoundaries (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Submodule R (chainCycles C n) :=
  LinearMap.range (chainBoundaryMap C n)

/-- The usual quotient of cycles by boundaries is the categorical homology. -/
def homologyQuotientIso (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    C.homology n ≅ ModuleCat.of R (chainCycles C n ⧸ chainBoundaries C n) :=
  (C.sc n).moduleCatHomologyIso

/-- The homology class of a chain cycle. -/
def chainClass (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    chainCycles C n →ₗ[R] C.homology n :=
  (homologyQuotientIso C n).toLinearEquiv.symm.toLinearMap.comp
    (chainBoundaries C n).mkQ

@[simp]
theorem mem_chainCycles_iff_succ (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x : C.X (n + 1)) :
    x ∈ chainCycles C (n + 1) ↔ (C.d (n + 1) n) x = 0 := by
  change (C.d (n + 1) ((ComplexShape.down ℕ).next (n + 1))) x = 0 ↔ _
  rw [(ComplexShape.down ℕ).next_eq'
    (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)]

/-- Every degree-zero chain is a cycle in a nonnegative chain complex. -/
theorem mem_chainCycles_zero (C : ChainComplex (ModuleCat.{0} R) ℕ) (x : C.X 0) :
    x ∈ chainCycles C 0 := by
  change (C.d 0 ((ComplexShape.down ℕ).next 0)) x = 0
  rw [C.shape 0 _ (Nat.succ_ne_zero _)]
  rfl

@[simp]
theorem chainCycles_zero_eq_top (C : ChainComplex (ModuleCat.{0} R) ℕ) :
    chainCycles C 0 = ⊤ := by
  ext x
  simp only [Submodule.mem_top, iff_true]
  exact mem_chainCycles_zero C x

/-- Every differential of a cycle vanishes, including off-shape differentials. -/
theorem chainCycle_d_eq_zero (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (n i : ℕ) (x : chainCycles C n) : (C.d n i) (x : C.X n) = 0 := by
  by_cases h : (ComplexShape.down ℕ).Rel n i
  · have hx : (C.d n ((ComplexShape.down ℕ).next n)) (x : C.X n) = 0 := x.property
    have hi : (ComplexShape.down ℕ).next n = i := (ComplexShape.down ℕ).next_eq' h
    rw [hi] at hx
    exact hx
  · rw [C.shape n i h]
    rfl

/-- Agreement of the explicit class map with the categorical projection. -/
theorem chainClass_eq_homologyπ (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x : chainCycles C n) :
    chainClass C n x = (C.homologyπ n) ((C.sc n).moduleCatCyclesIso.inv x) := by
  change (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatLeftHomologyData.π x) =
    (C.sc n).homologyπ ((C.sc n).moduleCatCyclesIso.inv x)
  exact (ConcreteCategory.congr_hom ((C.sc n).moduleCatCyclesIso_inv_π) x).symm

theorem chainClass_surjective (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Function.Surjective (chainClass C n) :=
  (homologyQuotientIso C n).toLinearEquiv.symm.surjective.comp
    (chainBoundaries C n).mkQ_surjective

theorem chainClass_eq_iff (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x y : chainCycles C n) :
    chainClass C n x = chainClass C n y ↔ x - y ∈ chainBoundaries C n := by
  change (homologyQuotientIso C n).toLinearEquiv.symm ((chainBoundaries C n).mkQ x) =
      (homologyQuotientIso C n).toLinearEquiv.symm ((chainBoundaries C n).mkQ y) ↔ _
  rw [(homologyQuotientIso C n).toLinearEquiv.symm.injective.eq_iff]
  exact Submodule.Quotient.eq _

@[simp]
theorem chainClass_eq_zero_iff (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x : chainCycles C n) :
    chainClass C n x = 0 ↔ x ∈ chainBoundaries C n := by
  simpa using chainClass_eq_iff C n x 0

@[simp]
theorem chainClass_boundary (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x : (C.sc n).X₁) :
    chainClass C n (chainBoundaryMap C n x) = 0 := by
  apply (chainClass_eq_zero_iff C n _).mpr
  exact ⟨x, rfl⟩

/-- Equality of homology classes is witnessed by an actual chain one degree higher. -/
theorem chainClass_eq_iff_exists (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x y : chainCycles C n) :
    chainClass C n x = chainClass C n y ↔
      ∃ z : C.X (n + 1), (C.d (n + 1) n) z =
        (x : C.X n) - (y : C.X n) := by
  rw [chainClass_eq_iff]
  have h : (x - y ∈ chainBoundaries C n) ↔
      ∃ z : (C.sc n).X₁, (C.sc n).f z = (x : C.X n) - (y : C.X n) := by
    change (∃ z, chainBoundaryMap C n z = x - y) ↔ _
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, congrArg Subtype.val hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, Subtype.ext hz⟩
  rw [h]
  change (∃ z : C.X ((ComplexShape.down ℕ).prev n),
    (C.d ((ComplexShape.down ℕ).prev n) n) z =
      (x : C.X n) - (y : C.X n)) ↔ _
  rw [(ComplexShape.down ℕ).prev_eq'
    (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)]

/-- A cycle has zero homology class precisely when it is a boundary. -/
theorem chainClass_eq_zero_iff_exists (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x : chainCycles C n) :
    chainClass C n x = 0 ↔ ∃ z : C.X (n + 1), (C.d (n + 1) n) z = (x : C.X n) := by
  simpa using chainClass_eq_iff_exists C n x 0

end

end OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives

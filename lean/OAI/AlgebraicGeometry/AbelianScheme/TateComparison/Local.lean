import Mathlib

/-! # Local -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Local

noncomputable section

/-!
Concrete local objects for TateComparison. Cocharacters record one common multiplier
and the three elementary divisors on each chosen side. Opposite lattices
are duals for the rescaled pairing; they are not independent input data.
No geometric realization or Hecke-action compatibility is assumed here.
-/

open scoped BigOperators Pointwise

/-- A dominant cocharacter of the split rank-three similitude group. -/
structure LocalType (s : ℕ) where
  multiplier : ℤ
  exponent : Fin s → Fin 3 → ℤ
  dominant : ∀ v, Antitone (exponent v)

namespace LocalType

/-- The integral range in IsogenyQuotient, including the opposite-side inequalities. -/
def IsIntegral {s : ℕ} (t : LocalType s) : Prop :=
  0 ≤ t.multiplier ∧ ∀ v i, 0 ≤ t.exponent v i ∧ t.exponent v i ≤ t.multiplier

/-- Multiplication by the central cocharacter with multiplier q². -/
def shift {s : ℕ} (t : LocalType s) (n : ℕ) : LocalType s where
  multiplier := t.multiplier + 2 * n
  exponent v i := t.exponent v i + n
  dominant v _ _ hij := by
    have := t.dominant v hij
    dsimp
    omega

/-- The scalar q on every chosen and opposite side. -/
def central (s : ℕ) : LocalType s where
  multiplier := 2
  exponent _ _ := 1
  dominant _ _ _ _ := le_rfl

theorem central_integral (s : ℕ) : (central s).IsIntegral := by
  constructor
  · norm_num [central]
  · intro v i
    norm_num [central]

/-- Central shifts clear all negative chosen-side and opposite-side exponents. -/
theorem exists_integral_shift {s : ℕ} (t : LocalType s) :
    ∃ n : ℕ, (t.shift n).IsIntegral := by
  let bound : ℕ := t.multiplier.natAbs + ∑ v : Fin s, ∑ i : Fin 3,
    (t.exponent v i).natAbs
  have hm : |t.multiplier| ≤ (bound : ℤ) := by
    dsimp [bound]
    rw [Int.natCast_natAbs]
    omega
  have he (v : Fin s) (i : Fin 3) : |t.exponent v i| ≤ (bound : ℤ) := by
    have h1 : (t.exponent v i).natAbs ≤
        ∑ j : Fin 3, (t.exponent v j).natAbs :=
      Finset.single_le_sum (f := fun j : Fin 3 => (t.exponent v j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : (∑ j : Fin 3, (t.exponent v j).natAbs) ≤
        ∑ w : Fin s, ∑ j : Fin 3, (t.exponent w j).natAbs :=
      Finset.single_le_sum (f := fun w : Fin s => ∑ j : Fin 3,
        (t.exponent w j).natAbs) (fun w _ => Nat.zero_le _) (Finset.mem_univ v)
    have h3 : (t.exponent v i).natAbs ≤ bound :=
      (h1.trans h2).trans (Nat.le_add_left _ _)
    simpa only [Int.natCast_natAbs] using Int.ofNat_le.mpr h3
  refine ⟨2 * bound, ?_, ?_⟩
  · dsimp [LocalType.shift]
    have := (abs_le.mp hm).1
    omega
  · intro v i
    have ha := abs_le.mp (he v i)
    have hb := abs_le.mp hm
    dsimp [LocalType.shift]
    constructor <;> omega

end LocalType

/-- Integral operators are a subtype, not a second unrelated index type. -/
abbrev IntegralType (s : ℕ) := {t : LocalType s // t.IsIntegral}

/-- Cumulative multiplier along a finite chain, including its initial stage. -/
def cumulativeMultiplier {s : ℕ} (ts : List (IntegralType s))
    (k : Fin (ts.length + 1)) : ℤ :=
  ((ts.take k.val).map fun t => t.val.multiplier).sum

section Lattices

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- A full lattice, using Mathlib's finite-generation and spanning predicate. -/
abbrev FullLattice := {L : Submodule R V // Submodule.IsLattice K L}

/-- The opposite lattice at multiplier m is the dual for m times the pairing. -/
def oppositeLattice (B : LinearMap.BilinForm K V) (m : K)
    (L : Submodule R V) : Submodule R V :=
  (m • B).dualSubmodule L

/-- Rescaling the pairing forces inverse rescaling of the dual lattice. -/
theorem oppositeLattice_eq_inverse_smul
    (B : LinearMap.BilinForm K V) (m : Kˣ) (L : Submodule R V) :
    oppositeLattice B (m : K) L = m⁻¹ • B.dualSubmodule L := by
  ext x
  change _ ↔ x ∈ m⁻¹ • (B.dualSubmodule L : Set V)
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [inv_inv]
  change (∀ y ∈ L, (m : K) * B x y ∈ (1 : Submodule R K)) ↔
    ∀ y ∈ L, B ((m : K) • x) y ∈ (1 : Submodule R K)
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- Dual lattices reverse inclusion, as required for opposite kernels. -/
theorem oppositeLattice_antitone (B : LinearMap.BilinForm K V) (m : K) :
    Antitone (oppositeLattice (R := R) B m) := by
  intro L M hLM x hx y hy
  exact hx y (hLM hy)

end Lattices

variable {R K V : Type*} [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [Module.IsTorsionFree R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- The pairing map between actual lattices, with integrality expressed as
membership in R. Its codomain is the R-linear dual of the chosen lattice. -/
def latticePairingMap (B : LinearMap.BilinForm K V) (L M : Submodule R V)
    (hIntegral : M ≤ B.dualSubmodule L) : M →ₗ[R] Module.Dual R L :=
  (B.dualSubmoduleToDual L).comp (Submodule.inclusion hIntegral)

/-- Perfectness means that the integral pairing identifies the opposite
lattice with the R-linear dual; no equality of ambient lattices is assumed. -/
def IsPerfectLatticePairing (B : LinearMap.BilinForm K V)
    (L M : Submodule R V) : Prop :=
  ∃ hIntegral : M ≤ B.dualSubmodule L,
    Function.Bijective (latticePairingMap B L M hIntegral)

/-- Perfectness and spanning force the entire opposite lattice. -/
theorem perfectLatticePairing_forces_dual
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (L M : Submodule R V) (hL : Submodule.span K (L : Set V) = ⊤)
    (h : IsPerfectLatticePairing B L M) : M = B.dualSubmodule L := by
  obtain ⟨hIntegral, _, hsurj⟩ := h
  apply le_antisymm hIntegral
  intro x hx
  obtain ⟨m, hm⟩ := hsurj (B.dualSubmoduleToDual L ⟨x, hx⟩)
  have heq : (Submodule.inclusion hIntegral) m = (⟨x, hx⟩ : B.dualSubmodule L) :=
    B.dualSubmoduleToDual_injective hB L hL hm
  have hv : m.val = x := congrArg Subtype.val heq
  exact hv ▸ m.property

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Local

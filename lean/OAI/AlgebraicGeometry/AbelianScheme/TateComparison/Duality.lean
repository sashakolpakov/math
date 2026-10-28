import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Local

/-! # Duality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality

noncomputable section

section

/-!
The canonical opposite lattice is constructed from a basis. Perfectness is
proved by extending an R-linear functional to K and using the nondegenerate
ambient pairing. This supplies existence as well as the uniqueness proved
in Local; it does not store the desired dual-lattice identity as data.
-/

open scoped BigOperators

variable {R K V : Type*} [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [Module.IsTorsionFree R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [FiniteDimensional K V]

/-- A finite K-basis spans a full R-lattice. -/
def latticeOfBasis {ι : Type*} [Finite ι] (e : Module.Basis ι K V) :
    Local.FullLattice (R := R) (K := K) (V := V) :=
  ⟨Submodule.span R (Set.range e),
    ⟨Submodule.fg_span (Set.finite_range e), by
      rw [Submodule.span_span_of_tower, e.span_eq]⟩⟩

/-- The dual lattice is full, with basis given by the ambient dual basis. -/
def dualLatticeOfBasis {ι : Type*} [Finite ι] [DecidableEq ι]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (e : Module.Basis ι K V) : Local.FullLattice (R := R) (K := K) (V := V) :=
  ⟨B.dualSubmodule (Submodule.span R (Set.range e)), by
    rw [B.dualSubmodule_span_of_basis hB e]
    exact (latticeOfBasis (R := R) (B.dualBasis hB e)).property⟩

/-- The R-linear dual pairing for a based lattice is surjective. -/
theorem dualPairing_surjective_of_basis {ι : Type*} [Finite ι] [DecidableEq ι]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (e : Module.Basis ι K V) :
    Function.Surjective
      (B.dualSubmoduleToDual (Submodule.span R (Set.range e))) := by
  let L := Submodule.span R (Set.range e)
  let b := e.restrictScalars R
  intro φ
  let fK : Module.Dual K V := e.constr K (fun i => algebraMap R K (φ (b i)))
  let y : V := (B.toDual hB).symm fK
  have heq : ((B y).restrictScalars R).comp L.subtype =
      (Algebra.linearMap R K).comp φ := by
    apply b.ext
    intro i
    simp [y, fK, b, L]
  have hy : y ∈ B.dualSubmodule L := by
    intro x hx
    apply Submodule.mem_one.mpr
    exact ⟨φ ⟨x, hx⟩, (LinearMap.congr_fun heq ⟨x, hx⟩).symm⟩
  refine ⟨⟨y, hy⟩, ?_⟩
  apply LinearMap.ext
  intro x
  apply FaithfulSMul.algebraMap_injective R K
  change algebraMap R K (B.dualSubmoduleParing ⟨y, hy⟩ x) = algebraMap R K (φ x)
  rw [B.dualSubmoduleParing_spec]
  exact LinearMap.congr_fun heq x

/-- The canonical dual is perfectly paired with its chosen-side lattice. -/
theorem dualLatticeOfBasis_perfect {ι : Type*} [Finite ι] [DecidableEq ι]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (e : Module.Basis ι K V) :
    Local.IsPerfectLatticePairing B (latticeOfBasis (R := R) e).val
      (dualLatticeOfBasis (R := R) B hB e).val := by
  refine ⟨le_rfl, ?_, ?_⟩
  · change Function.Injective
      ((B.dualSubmoduleToDual (Submodule.span R (Set.range e))).comp
        (Submodule.inclusion le_rfl))
    apply Function.Injective.comp
    · exact B.dualSubmoduleToDual_injective hB _
        (latticeOfBasis (R := R) e).property.span_eq_top
    · exact Submodule.inclusion_injective le_rfl
  · intro φ
    obtain ⟨y, hy⟩ := dualPairing_surjective_of_basis (R := R) B hB e φ
    exact ⟨y, hy⟩

end

/-!
ElementaryDivisors is a named proposition input, not an imported theorem stub. Its lattice
clause supplies bases; the dual-lattice constructors and all identifications
below are proved. The local paired-lattice system has a perfect-pairing
condition, not an assumed formula for its opposite lattice.
-/

open scoped BigOperators Pointwise

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The complete elementary-divisor clause of the supplied ElementaryDivisors specification.
The two lattice typeclass binders are written as explicit proposition arguments. -/
def ElementaryDivisorsInput : Prop :=
  ∀ {n : ℕ} (π : R), Irreducible π →
    ∀ (L M : Submodule R (Fin n → K)),
      Submodule.IsLattice K L → Submodule.IsLattice K M →
      ∃! a : Fin n → ℤ,
        Monotone a ∧
        ∃ e : Module.Basis (Fin n) K (Fin n → K),
          L = Submodule.span R (Set.range e) ∧
          M = Submodule.span R
            (Set.range fun i => (algebraMap R K π) ^ a i • e i)

abbrev RankThreeLattice := Local.FullLattice (R := R) (K := K) (V := Fin 3 → K)

variable {R K}

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- ElementaryDivisors supplies an actual basis for each chosen-side lattice. -/
theorem rankThreeLattice_basis (hElementaryDivisors : ElementaryDivisorsInput R K) (π : R) (hπ : Irreducible π)
    (L : RankThreeLattice R K) :
    ∃ e : Module.Basis (Fin 3) K (Fin 3 → K),
      L.val = Submodule.span R (Set.range e) := by
  obtain ⟨_, ⟨_, e, he, _⟩, _⟩ := hElementaryDivisors π hπ L.val L.val L.property L.property
  exact ⟨e, he⟩

/-- The full opposite lattice is constructed using the ElementaryDivisors basis. -/
def dualFullLattice (hElementaryDivisors : ElementaryDivisorsInput R K) (π : R) (hπ : Irreducible π)
    (B : LinearMap.BilinForm K (Fin 3 → K)) (hB : B.Nondegenerate)
    (L : RankThreeLattice R K) : RankThreeLattice R K := by
  refine ⟨B.dualSubmodule L.val, ?_⟩
  obtain ⟨e, he⟩ := rankThreeLattice_basis hElementaryDivisors π hπ L
  rw [he]
  exact (dualLatticeOfBasis (R := R) B hB e).property

theorem dualFullLattice_perfect (hElementaryDivisors : ElementaryDivisorsInput R K) (π : R) (hπ : Irreducible π)
    (B : LinearMap.BilinForm K (Fin 3 → K)) (hB : B.Nondegenerate)
    (L : RankThreeLattice R K) :
    Local.IsPerfectLatticePairing B L.val (dualFullLattice hElementaryDivisors π hπ B hB L).val := by
  change Local.IsPerfectLatticePairing B L.val (B.dualSubmodule L.val)
  obtain ⟨e, he⟩ := rankThreeLattice_basis hElementaryDivisors π hπ L
  rw [he]
  exact dualLatticeOfBasis_perfect B hB e

/-- A nonzero scalar multiple retains the nondegeneracy of the actual pairing. -/
theorem nondegenerate_unit_smul {V : Type*} [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (m : Kˣ) :
    ((m : K) • B).Nondegenerate := by
  constructor
  · intro x hx
    apply hB.1 x
    intro y
    exact (mul_eq_zero.mp (hx y)).resolve_left m.ne_zero
  · intro y hy
    apply hB.2 y
    intro x
    exact (mul_eq_zero.mp (hy x)).resolve_left m.ne_zero

variable (R K)

/-- Paired lattice data at finitely many stages, with the geometric
perfectness condition for each rescaled polarization pairing. -/
structure PairedLatticeSystem (s n : ℕ)
    (B : Fin s → LinearMap.BilinForm K (Fin 3 → K)) (m : Fin n → Kˣ) where
  chosen : Fin n → Fin s → RankThreeLattice R K
  opposite : Fin n → Fin s → RankThreeLattice R K
  perfect : ∀ k v,
    Local.IsPerfectLatticePairing ((m k : K) • B v) (chosen k v).val (opposite k v).val

variable {R K} {s n : ℕ}
  {B : Fin s → LinearMap.BilinForm K (Fin 3 → K)} {m : Fin n → Kˣ}

namespace PairedLatticeSystem

/-- Perfectness proves the manuscript's inverse-multiplier dual-lattice formula. -/
theorem opposite_forced (D : PairedLatticeSystem R K s n B m)
    (hB : ∀ v, (B v).Nondegenerate) (k : Fin n) (v : Fin s) :
    (D.opposite k v).val = (m k)⁻¹ • (B v).dualSubmodule (D.chosen k v).val := by
  have h := Local.perfectLatticePairing_forces_dual ((m k : K) • B v)
    (nondegenerate_unit_smul (B v) (hB v) (m k))
    (D.chosen k v).val (D.opposite k v).val
    (D.chosen k v).property.span_eq_top (D.perfect k v)
  exact h.trans (Local.oppositeLattice_eq_inverse_smul (B v) (m k) (D.chosen k v).val)

/-- The canonical lift of any chosen-side lattice system. -/
def ofChosen (hElementaryDivisors : ElementaryDivisorsInput R K) (π : R) (hπ : Irreducible π)
    (hB : ∀ v, (B v).Nondegenerate)
    (L : Fin n → Fin s → RankThreeLattice R K) : PairedLatticeSystem R K s n B m where
  chosen := L
  opposite k v := dualFullLattice hElementaryDivisors π hπ ((m k : K) • B v)
    (nondegenerate_unit_smul (B v) (hB v) (m k)) (L k v)
  perfect k v := dualFullLattice_perfect hElementaryDivisors π hπ ((m k : K) • B v)
    (nondegenerate_unit_smul (B v) (hB v) (m k)) (L k v)

theorem chosen_injective (hB : ∀ v, (B v).Nondegenerate) :
    Function.Injective (chosen (R := R) (K := K) (s := s) (n := n) (B := B) (m := m)) := by
  intro D E he
  have ho : D.opposite = E.opposite := by
    funext k v
    apply Subtype.ext
    rw [D.opposite_forced hB, E.opposite_forced hB, he]
  cases D
  cases E
  cases he
  cases ho
  rfl

/-- Local paired systems are equivalent to independent chosen-side systems.
Restricting by prescribed chosen-side relative positions gives the flag version. -/
def chosenEquiv (hElementaryDivisors : ElementaryDivisorsInput R K) (π : R) (hπ : Irreducible π)
    (hB : ∀ v, (B v).Nondegenerate) :
    PairedLatticeSystem R K s n B m ≃
      (Fin n → Fin s → RankThreeLattice R K) where
  toFun := chosen
  invFun := ofChosen hElementaryDivisors π hπ hB
  left_inv _ := chosen_injective hB rfl
  right_inv _ := rfl

end PairedLatticeSystem

/-- The superlattice convention: inverse diagonal representatives extend L
by the elementary divisors q^a. -/
def RelativePosition (π : R) (a : Fin 3 → ℤ)
    (L M : RankThreeLattice R K) : Prop :=
  ∃ e : Module.Basis (Fin 3) K (Fin 3 → K),
    L.val = Submodule.span R (Set.range e) ∧
    M.val = Submodule.span R
      (Set.range fun i => (algebraMap R K π) ^ (-a i) • e i)

/-- Ordinary independent GL₃ flags, with their precise initial lattice and
their prescribed elementary-divisor steps. -/
def IsChosenBlockFlag (π : R) (L₀ : Fin s → RankThreeLattice R K)
    (ts : List (Local.IntegralType s))
    (L : Fin (ts.length + 1) → Fin s → RankThreeLattice R K) : Prop :=
  L 0 = L₀ ∧ ∀ (k : Fin ts.length) (v : Fin s),
    RelativePosition π ((ts.get k).val.exponent v) (L k.castSucc v) (L k.succ v)

abbrev LinearBlockFlags (π : R) (L₀ : Fin s → RankThreeLattice R K)
    (ts : List (Local.IntegralType s)) :=
  {L // IsChosenBlockFlag π L₀ ts L}

/-- Polarized local flags. The only extra condition is perfectness of the
rescaled pairings; their opposite lattices are not supplied by a formula. -/
abbrev PairedBlockFlags (π : R) (u : Kˣ)
    (B : Fin s → LinearMap.BilinForm K (Fin 3 → K))
    (L₀ : Fin s → RankThreeLattice R K) (ts : List (Local.IntegralType s)) :=
  {D : PairedLatticeSystem R K s (ts.length + 1) B
    (fun k => u ^ Local.cumulativeMultiplier ts k) // IsChosenBlockFlag π L₀ ts D.chosen}

/-- The local flag equivalence, conditional on the identified ElementaryDivisors input.
For the application u is q in Q_q and π is q in Z_q. -/
def pairedBlockFlagsEquiv (hElementaryDivisors : ElementaryDivisorsInput R K) (π : R) (hπ : Irreducible π)
    (u : Kˣ) (B : Fin s → LinearMap.BilinForm K (Fin 3 → K))
    (hB : ∀ v, (B v).Nondegenerate) (L₀ : Fin s → RankThreeLattice R K)
    (ts : List (Local.IntegralType s)) :
    PairedBlockFlags π u B L₀ ts ≃ LinearBlockFlags π L₀ ts where
  toFun D := ⟨D.val.chosen, D.property⟩
  invFun L := ⟨PairedLatticeSystem.ofChosen hElementaryDivisors π hπ hB L.val, L.property⟩
  left_inv _ := Subtype.ext (PairedLatticeSystem.chosen_injective hB rfl)
  right_inv _ := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality

import OAI.RepresentationTheory.Weil.Local.Uniformizer
import OAI.RepresentationTheory.Weil.Local.CompactSquareComparison
import Mathlib.Data.ZMod.QuotientGroup

/-! # Finite Square Classes -/

namespace OAI.RepresentationTheory.Weil.Local.FiniteSquareClasses.Construction

noncomputable section

section

/-! The valuation contributes one additional factor of two to the local field square classes. -/

theorem squareUnitsSubgroup_prod {G H : Type*} [CommGroup G] [CommGroup H] :
    QuadraticNormSubgroup.Construction.squareUnitsSubgroup (G × H) = (QuadraticNormSubgroup.Construction.squareUnitsSubgroup G).prod (QuadraticNormSubgroup.Construction.squareUnitsSubgroup H) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.1, rfl⟩, ⟨y.2, rfl⟩⟩
  · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    exact ⟨(y, z), Prod.ext hy hz⟩

theorem multiplicativeInt_square_index : (QuadraticNormSubgroup.Construction.squareUnitsSubgroup (Multiplicative ℤ)).index = 2 := by
  let f : Multiplicative ℤ →* Multiplicative (ZMod 2) :=
    (Int.castAddHom (ZMod 2)).toMultiplicative
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective (Multiplicative.toAdd x)
    exact ⟨Multiplicative.ofAdd n, congrArg Multiplicative.ofAdd hn⟩
  have hker : f.ker = QuadraticNormSubgroup.Construction.squareUnitsSubgroup (Multiplicative ℤ) := by
    ext x
    constructor
    · intro hx
      have hh : ((Multiplicative.toAdd x : ℤ) : ZMod 2) = 0 := congrArg Multiplicative.toAdd hx
      obtain ⟨n, hn⟩ := (ZMod.intCast_eq_zero_iff_even).mp hh
      refine ⟨Multiplicative.ofAdd n, ?_⟩
      change (Multiplicative.ofAdd n) ^ 2 = x
      rw [pow_two]
      exact congrArg Multiplicative.ofAdd hn.symm
    · rintro ⟨y, rfl⟩
      change Multiplicative.ofAdd ((2 * Multiplicative.toAdd y : ℤ) : ZMod 2) = 1
      apply congrArg Multiplicative.ofAdd
      rw [Int.cast_mul]
      change (2 : ZMod 2) * (Multiplicative.toAdd y : ℤ) = 0
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]
  rw [← hker, Subgroup.index_ker, f.range_eq_top_of_surjective hsurj]
  simp

theorem localField_square_index_eq_twice_normUnit
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k]
    (hnd : ¬ DiscreteTopology k) :
    (QuadraticNormSubgroup.Construction.squareUnitsSubgroup kˣ).index = 2 * (QuadraticNormSubgroup.Construction.squareUnitsSubgroup (PrincipalSquareClasses.Construction.normUnitSubgroup k)).index := by
  obtain ⟨e⟩ := Uniformizer.Construction.exists_localUnits_decomposition hnd
  rw [SquareIndexTools.Construction.square_index_mulEquiv e, squareUnitsSubgroup_prod, Subgroup.index_prod,
    multiplicativeInt_square_index, Nat.mul_comm]

theorem localField_square_index_eq_twice_normOne
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [IsUltrametricDist k] (hnd : ¬ DiscreteTopology k) (h : ¬ ∃ t : k, t ^ 2 = -1) :
    (QuadraticNormSubgroup.Construction.squareUnitsSubgroup kˣ).index = 2 * (QuadraticNormSubgroup.Construction.squareUnitsSubgroup (QuadraticNormAt.Construction.QuadraticNormOne k)).index := by
  rw [localField_square_index_eq_twice_normUnit hnd, CompactSquareComparison.Construction.normUnit_normOne_square_index_eq hnd h]

end

/-! Finiteness and nonzero indices for the local square-class groups. -/

open Set

theorem normUnit_square_subgroupOf
    {k : Type*} [NormedField k] :
    (QuadraticNormSubgroup.Construction.squareUnitsSubgroup kˣ).subgroupOf (PrincipalSquareClasses.Construction.normUnitSubgroup k) =
      QuadraticNormSubgroup.Construction.squareUnitsSubgroup (PrincipalSquareClasses.Construction.normUnitSubgroup k) := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    have hx : ‖x.val.val‖ = 1 := x.property
    have hval : y.val ^ 2 = x.val.val := congrArg Units.val hy
    have hn : ‖y.val‖ ^ 2 = 1 := by rw [← norm_pow, hval, hx]
    have hy1 : ‖y.val‖ = 1 := by nlinarith [norm_nonneg y.val]
    exact ⟨⟨y, hy1⟩, Subtype.ext hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y.val, congrArg Subtype.val hy⟩

theorem normUnit_square_index_ne_zero
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    (hnd : ¬ DiscreteTopology k) : (QuadraticNormSubgroup.Construction.squareUnitsSubgroup (PrincipalSquareClasses.Construction.normUnitSubgroup k)).index ≠ 0 := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField k with hd | ⟨_, rfl⟩
  · exact (hnd hd).elim
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hnd
  let : CompactSpace (PrincipalSquareClasses.Construction.normUnitSubgroup k) := isCompact_iff_compactSpace.mp PrincipalSquareClasses.Construction.normUnitSubgroup_isCompact
  have ho : IsOpen (QuadraticNormSubgroup.Construction.squareUnitsSubgroup (PrincipalSquareClasses.Construction.normUnitSubgroup k) : Set (PrincipalSquareClasses.Construction.normUnitSubgroup k)) := by
    rw [← normUnit_square_subgroupOf]
    exact Subgroup.subgroupOf_isOpen _ _ QuadraticNormSubgroup.Construction.squareUnitsSubgroup_isOpen
  let : Finite (PrincipalSquareClasses.Construction.normUnitSubgroup k ⧸ QuadraticNormSubgroup.Construction.squareUnitsSubgroup (PrincipalSquareClasses.Construction.normUnitSubgroup k)) :=
    Subgroup.quotient_finite_of_isOpen _ ho
  exact (QuadraticNormSubgroup.Construction.squareUnitsSubgroup (PrincipalSquareClasses.Construction.normUnitSubgroup k)).index_ne_zero_of_finite

theorem localField_square_index_ne_zero
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [IsUltrametricDist k] (hnd : ¬ DiscreteTopology k) : (QuadraticNormSubgroup.Construction.squareUnitsSubgroup kˣ).index ≠ 0 := by
  rw [localField_square_index_eq_twice_normUnit hnd]
  exact mul_ne_zero (by decide) (normUnit_square_index_ne_zero hnd)

theorem normOne_square_index_ne_zero
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [IsUltrametricDist k] (hnd : ¬ DiscreteTopology k) (h : ¬ ∃ t : k, t ^ 2 = -1) :
    (QuadraticNormSubgroup.Construction.squareUnitsSubgroup (QuadraticNormAt.Construction.QuadraticNormOne k)).index ≠ 0 := by
  rw [← CompactSquareComparison.Construction.normUnit_normOne_square_index_eq hnd h]
  exact normUnit_square_index_ne_zero hnd

end

end OAI.RepresentationTheory.Weil.Local.FiniteSquareClasses.Construction

import OAI.RepresentationTheory.Theta.Adelic.QuadraticNormIndex
import OAI.RepresentationTheory.Theta.Adelic.SplitNorm

/-! # Quadratic Norm Character -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter

noncomputable section

/-! The actual quadratic norm criterion defines a continuous character at
each nonarchimedean local field, including split quadratic algebras. -/

open scoped Classical

open Set
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient OAI.RepresentationTheory.Theta.Adelic.QuadraticNormIndex

def normSign {k : Type*} [Field k] (d : k) (a : kˣ) : Circle :=
  if a ∈ (QuadraticNormSquareQuotient.normUnits d).range then 1 else -1

theorem circle_minus_one_ne_one : (-1 : Circle) ≠ 1 := by
  intro h
  have hc := congrArg (fun z : Circle => (z : ℂ)) h
  norm_num at hc

theorem normSign_eq_one_iff {k : Type*} [Field k] (d : k) (a : kˣ) :
    normSign d a = 1 ↔ a ∈ (QuadraticNormSquareQuotient.normUnits d).range := by
  by_cases h : a ∈ (QuadraticNormSquareQuotient.normUnits d).range
  · simp [normSign, h]
  · simp [normSign, h, circle_minus_one_ne_one]

theorem normSign_one {k : Type*} [Field k] (d : k) : normSign d 1 = 1 :=
  (normSign_eq_one_iff d 1).mpr (Subgroup.one_mem _)

theorem normSign_mul_of_index_two {k : Type*} [Field k] (d : k)
    (hindex : (QuadraticNormSquareQuotient.normUnits d).range.index = 2) (a b : kˣ) :
    normSign d (a * b) = normSign d a * normSign d b := by
  by_cases ha : a ∈ (QuadraticNormSquareQuotient.normUnits d).range <;> by_cases hb : b ∈ (QuadraticNormSquareQuotient.normUnits d).range <;>
    simp [normSign, (QuadraticNormSquareQuotient.normUnits d).range.mul_mem_iff_of_index_two hindex, ha, hb]

theorem normSign_split {k : Type*} [Field k] [CharZero k]
    (d : k) (hd : d ≠ 0) (hsq : IsSquare d) (a : kˣ) : normSign d a = 1 := by
  obtain ⟨r, hr⟩ := hsq
  have hr2 : r ^ 2 = d := by simpa only [pow_two] using hr.symm
  have hr0 : r ≠ 0 := by intro hz; apply hd; simpa [hz] using hr2.symm
  apply (normSign_eq_one_iff d a).mpr
  exact SplitNorm.norm_units_surjective r hr2 hr0 a

theorem normRange_isOpen
    {k : Type} [NormedField k] [CompleteSpace k] [CharZero k]
    (d : k) (hnd : ¬ DiscreteTopology k) : IsOpen ((QuadraticNormSquareQuotient.normUnits d).range : Set kˣ) := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField k with hd | ⟨_, rfl⟩
  · exact (hnd hd).elim
  · exact Subgroup.isOpen_mono (QuadraticNormIndex.squareUnitsSubgroup_le_normRange d) Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup_isOpen

theorem normSign_continuous
    {k : Type} [NormedField k] [CompleteSpace k] [CharZero k]
    (d : k) (hnd : ¬ DiscreteTopology k) : Continuous (normSign d) := by
  have ho := normRange_isOpen d hnd
  have hc : IsClopen ((QuadraticNormSquareQuotient.normUnits d).range : Set kˣ) :=
    ⟨(QuadraticNormSquareQuotient.normUnits d).range.isClosed_of_isOpen ho, ho⟩
  apply Continuous.if (p := fun a => a ∈ (QuadraticNormSquareQuotient.normUnits d).range) _ continuous_const continuous_const
  intro a ha
  change a ∈ frontier ((QuadraticNormSquareQuotient.normUnits d).range : Set kˣ) at ha
  rw [hc.frontier_eq] at ha
  exact ha.elim

theorem normSign_mul
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [IsUltrametricDist k] (d : k) (hd : d ≠ 0) (hnd : ¬ DiscreteTopology k) (a b : kˣ) :
    normSign d (a * b) = normSign d a * normSign d b := by
  by_cases hsq : IsSquare d
  · rw [normSign_split d hd hsq, normSign_split d hd hsq, normSign_split d hd hsq, one_mul]
  · exact normSign_mul_of_index_two d
      (QuadraticNormIndex.localField_quadraticNorm_index_two d hd hnd hsq) a b

def nonarchimedeanNormCharacter
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [IsUltrametricDist k] (d : k) (hd : d ≠ 0) (hnd : ¬ DiscreteTopology k) : kˣ →ₜ* Circle where
  toFun := normSign d
  map_one' := normSign_one d
  map_mul' := normSign_mul d hd hnd
  continuous_toFun := normSign_continuous d hnd

theorem nonarchimedeanNormCharacter_kernel
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [IsUltrametricDist k] (d : k) (hd : d ≠ 0) (hnd : ¬ DiscreteTopology k) (a : kˣ) :
    nonarchimedeanNormCharacter d hd hnd a = 1 ↔
      ∃ b : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ, Units.map QuadraticAlgebra.norm b = a :=
  normSign_eq_one_iff d a

theorem normSign_eq_normCharacter (F : Type) [Field F] [NumberField F]
    (d : F) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ) :
    normSign (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) a = Weil.AdelicSplitting.Characters.Construction.normCharacter F d v a := rfl

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter

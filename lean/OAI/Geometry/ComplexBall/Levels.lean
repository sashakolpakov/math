import OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData
import OAI.NumberTheory.ArithmeticGroups.Lattice

/-! # Levels -/

namespace OAI.Geometry.ComplexBall.Levels.ArithmeticQuotient

noncomputable section

/-! The exact matrix principal levels in ArithmeticQuotient agree with the full-lattice
conditions needed to apply the supplied TorsionFreeLevel proposition. -/

open scoped BigOperators Classical
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

/-- The supplied first TorsionFreeLevel proposition, kept as an explicit input. -/
def TorsionFreeLevelsInput (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] : Prop :=
  ∀ (b : E) (Λ : Submodule ℤ (ArithmeticQuotientEquationsData.Vec E)), NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ →
    ∀ N₀ : ℕ, 0 < N₀ →
      ∃ N : ℕ, 3 ≤ N ∧ N₀ ∣ N ∧
        ∀ M : ℕ, 0 < M → N ∣ M →
          ∀ g : ArithmeticQuotientEquationsData.Vec E ≃ₗ[E] ArithmeticQuotientEquationsData.Vec E,
            NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel b Λ M g →
            ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
lemma integral_adjugate (g : ArithmeticQuotientEquationsData.Mat E) (hg : ∀ i j, IsIntegral ℤ (g i j)) :
    ∀ i j, IsIntegral ℤ (g.adjugate i j) := by
  let A : ArithmeticQuotientEquationsData.Mat (NumberField.RingOfIntegers E) := fun i j => ⟨g i j, hg i j⟩
  have hm := (algebraMap (NumberField.RingOfIntegers E) E).map_adjugate A
  intro i j
  have hij := congrArg (fun M : ArithmeticQuotientEquationsData.Mat E => M i j) hm
  change (A.adjugate i j : E) = g.adjugate i j at hij
  rw [← hij]
  exact (A.adjugate i j).property

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
lemma integral_mulVec (g : ArithmeticQuotientEquationsData.Mat E) (hg : ∀ i j, IsIntegral ℤ (g i j))
    (x : ArithmeticQuotientEquationsData.Vec E) (hx : ∀ i, IsIntegral ℤ (x i)) :
    ∀ i, IsIntegral ℤ (g.mulVec x i) := by
  intro i
  change IsIntegral ℤ (∑ j, g i j * x j)
  exact IsIntegral.sum _ (fun j _ => (hg i j).mul (hx j))

omit [Algebra ℚ E] in
lemma principal_entries_integral (b : E) (N : ℕ) (g : ArithmeticQuotientEquationsData.Mat E)
    (hg : ArithmeticQuotientEquationsData.principalLevel b N g) : ∀ i j, IsIntegral ℤ (g i j) := by
  obtain ⟨B, hB⟩ := hg.2.2
  intro i j
  have hi : IsIntegral ℤ ((1 : ArithmeticQuotientEquationsData.Mat E) i j) := by
    by_cases h : i = j
    · simpa only [Matrix.one_apply, ite_eq_left h] using (isIntegral_one : IsIntegral ℤ (1 : E))
    · simpa only [Matrix.one_apply, ite_eq_right h] using (isIntegral_zero : IsIntegral ℤ (0 : E))
  have hn : IsIntegral ℤ (N : E) := isIntegral_natCast N
  rw [(sub_eq_iff_eq_add).mp (hB i j)]
  exact (hn.mul (B i j).property).add hi

omit [Algebra ℚ E] in
lemma matrixPrincipalLevel_to_lattice (b : E) (N : ℕ) (g : ArithmeticQuotientEquationsData.Mat E)
    (hg : ArithmeticQuotientEquationsData.principalLevel b N g) :
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel b (NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.standardLattice (E := E)) N
      (Matrix.SpecialLinearGroup.toLin' (⟨g, hg.1⟩ : ArithmeticQuotientEquationsData.SL E)) := by
  let s : ArithmeticQuotientEquationsData.SL E := ⟨g, hg.1⟩
  have hint := principal_entries_integral b N g hg
  refine ⟨hg.2.1, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      exact (NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.mem_standardLattice _).mpr
        (integral_mulVec g hint x ((NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.mem_standardLattice _).mp hx))
    · intro hx
      have hinv := integral_mulVec g.adjugate (integral_adjugate g hint)
        (g.mulVec x) ((NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.mem_standardLattice _).mp hx)
      have hc : g.adjugate.mulVec (g.mulVec x) = x := by
        change Matrix.SpecialLinearGroup.toLin' s⁻¹
          (Matrix.SpecialLinearGroup.toLin' s x) = x
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      rw [hc] at hinv
      exact (NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.mem_standardLattice _).mpr hinv
  · intro x hx
    obtain ⟨B, hB⟩ := hg.2.2
    let B' : ArithmeticQuotientEquationsData.Mat E := fun i j => (B i j : E)
    refine ⟨B'.mulVec x, ?_, ?_⟩
    · exact (NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.mem_standardLattice _).mpr
        (integral_mulVec B' (fun i j => (B i j).property) x
          ((NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.mem_standardLattice _).mp hx))
    · have hm : g - 1 = (N : E) • B' := by
        ext i j
        exact hB i j
      change g.mulVec x - x = (N : ℤ) • B'.mulVec x
      calc
        g.mulVec x - x = (g - 1).mulVec x := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        _ = ((N : E) • B').mulVec x := by rw [hm]
        _ = (N : ℤ) • B'.mulVec x := by
          rw [Matrix.smul_mulVec]
          ext i
          simp [smul_eq_mul]

/-- Arbitrarily deep torsion-free levels in the exact matrix formulation. -/
theorem matrix_levels_torsion_free (hTorsionFreeLevel : TorsionFreeLevelsInput E)
    (b : E) (N₀ : ℕ) (hN₀ : 0 < N₀) :
    ∃ N : ℕ, 0 < N ∧ N₀ ∣ N ∧
      ∀ g : ArithmeticQuotientEquationsData.Mat E, ArithmeticQuotientEquationsData.principalLevel b N g →
        ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1 := by
  obtain ⟨N, hN, hdiv, ht⟩ := hTorsionFreeLevel b (NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.standardLattice (E := E))
    NumberTheory.ArithmeticGroups.Lattice.CongruenceLevel.standardLattice_full_stable N₀ hN₀
  refine ⟨N, by omega, hdiv, ?_⟩
  intro g hg k hk hpow
  let s : ArithmeticQuotientEquationsData.SL E := ⟨g, hg.1⟩
  have hspow : s ^ k = 1 := Subtype.ext hpow
  have hlpow : (Matrix.SpecialLinearGroup.toLin' s) ^ k = 1 := by
    simpa only [map_pow, map_one] using
      congrArg Matrix.SpecialLinearGroup.toLin' hspow
  have he := ht N (by omega) (dvd_refl N) (Matrix.SpecialLinearGroup.toLin' s)
    (matrixPrincipalLevel_to_lattice b N g hg) k hk hlpow
  have hs : s = 1 := Matrix.SpecialLinearGroup.toLin'_injective (by simpa using he)
  exact congrArg (fun a : ArithmeticQuotientEquationsData.SL E => (a : ArithmeticQuotientEquationsData.Mat E)) hs

end

end OAI.Geometry.ComplexBall.Levels.ArithmeticQuotient

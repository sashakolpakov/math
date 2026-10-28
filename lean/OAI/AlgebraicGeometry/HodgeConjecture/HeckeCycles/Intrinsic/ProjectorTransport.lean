import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Comap
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiComparison

/-! # Projector Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ProjectorTransport.CM

noncomputable section

/-! Transport actual coefficient projectors to the same complex Betti
space used by GeometricComparison. Their ranges, nonvanishing, and Hodge preservation
follow from the canonical coefficient equivalence. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiComparison.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Comap.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
  (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq) (j : K →+* ℂ)

local instance : FiniteDimensional ℚ (A.Betti j) := (Constructed.Comap.CM.hodge A j).finiteDimensional

def projector (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j))) :
    Module.End ℂ (A.ComplexBetti j) := (BettiComparison.CM.coefficientEquiv A j).conj P

theorem projector_range (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j))) :
    LinearMap.range (projector A j P) = (LinearMap.range P).map (BettiComparison.CM.coefficientMap A j) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨P ((BettiComparison.CM.coefficientEquiv A j).symm x), ⟨_, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    refine ⟨BettiComparison.CM.coefficientEquiv A j z, ?_⟩
    change BettiComparison.CM.coefficientEquiv A j (P ((BettiComparison.CM.coefficientEquiv A j).symm (BettiComparison.CM.coefficientEquiv A j z))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl

theorem projector_idempotent (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j)))
    (hP : P * P = P) : projector A j P * projector A j P = projector A j P := by
  ext x
  change BettiComparison.CM.coefficientEquiv A j (P ((BettiComparison.CM.coefficientEquiv A j).symm
    (BettiComparison.CM.coefficientEquiv A j (P ((BettiComparison.CM.coefficientEquiv A j).symm x))))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact congrArg (BettiComparison.CM.coefficientEquiv A j) (LinearMap.congr_fun hP _)

theorem projector_preserves
    (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j)))
    (S : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j))) (B : Submodule ℂ (A.ComplexBetti j))
    (hS : S = B.comap (BettiComparison.CM.coefficientMap A j)) (hP : ∀ x ∈ S, P x ∈ S)
    (x : A.ComplexBetti j) (hx : x ∈ B) : projector A j P x ∈ B := by
  have hi : (BettiComparison.CM.coefficientEquiv A j).symm x ∈ S := by
    rw [hS]
    change BettiComparison.CM.coefficientEquiv A j ((BettiComparison.CM.coefficientEquiv A j).symm x) ∈ B
    rwa [LinearEquiv.apply_symm_apply]
  have hp := hP _ hi
  rw [hS] at hp
  exact hp

theorem projector_holomorphic
    (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j)))
    (hP : P ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace (Constructed.Comap.CM.hodge A j) (Constructed.Comap.CM.hodge A j)) :
    ∀ x ∈ A.bettiFiltration j (AbelianProjectivePresentation.CM.presentation A j) 1,
      projector A j P x ∈ A.bettiFiltration j (AbelianProjectivePresentation.CM.presentation A j) 1 :=
  projector_preserves A j P _ _ (Constructed.Comap.CM.holomorphic_comap A j) hP.1

theorem projector_antiholomorphic
    (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j)))
    (hP : P ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace (Constructed.Comap.CM.hodge A j) (Constructed.Comap.CM.hodge A j)) :
    ∀ x ∈ (A.smoothProjectiveFiber j (AbelianProjectivePresentation.CM.presentation A j)).pureBettiSubspace 0 1,
      projector A j P x ∈ (A.smoothProjectiveFiber j (AbelianProjectivePresentation.CM.presentation A j)).pureBettiSubspace 0 1 :=
  projector_preserves A j P _ _ (Constructed.Comap.CM.antiholomorphic_comap A j) hP.2

theorem complementary :
    IsCompl (A.bettiFiltration j (AbelianProjectivePresentation.CM.presentation A j) 1)
      ((A.smoothProjectiveFiber j (AbelianProjectivePresentation.CM.presentation A j)).pureBettiSubspace 0 1) := by
  have h := (Constructed.Comap.CM.hodge A j).complementary
  rw [Constructed.Comap.CM.holomorphic_comap, Constructed.Comap.CM.antiholomorphic_comap] at h
  exact (Submodule.orderIsoMapComap (BettiComparison.CM.coefficientEquiv A j)).symm.isCompl_iff.mpr h

theorem range_nonzero (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j)))
    (x : ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j)) (hx : P x ≠ 0) :
    LinearMap.range (projector A j P) ≠ ⊥ := by
  intro hz
  have hm : BettiComparison.CM.coefficientMap A j (P x) ∈ LinearMap.range (projector A j P) := by
    rw [projector_range]
    exact ⟨P x, ⟨x, rfl⟩, rfl⟩
  rw [hz, Submodule.mem_bot] at hm
  exact hx ((BettiComparison.CM.coefficientEquiv A j).map_eq_zero_iff.mp hm)

theorem range_of_character {H : Type} [CommRing H] [Algebra ℚ H]
    (ρ : A.HeckeRealization H) (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j)))
    (χ : H → ℂ)
    (hP : LinearMap.range P = HeckeCharacters.CM.Projectors.jointSpace (fun h => (Constructed.Comap.CM.heckeAction A j ρ h).baseChange ℂ) χ) :
    LinearMap.range (projector A j P) = A.bettiHeckeSummand j ρ χ := by
  rw [projector_range, hP]
  simp_rw [Constructed.Comap.CM.heckeAction_apply]
  exact BettiComparison.CM.Summands.betti_summand_identification A j ρ χ

theorem holomorphic_bound_iff (S : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j))) :
    S.map (BettiComparison.CM.coefficientMap A j) ≤ A.bettiFiltration j (AbelianProjectivePresentation.CM.presentation A j) 1 ↔
      S ≤ (Constructed.Comap.CM.hodge A j).holomorphic := by
  rw [Submodule.map_le_iff_le_comap, Constructed.Comap.CM.holomorphic_comap]

theorem antiholomorphic_bound_iff (S : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j))) :
    S.map (BettiComparison.CM.coefficientMap A j) ≤
        (A.smoothProjectiveFiber j (AbelianProjectivePresentation.CM.presentation A j)).pureBettiSubspace 0 1 ↔
      S ≤ (Constructed.Comap.CM.hodge A j).antiholomorphic := by
  let B : Submodule ℂ (A.ComplexBetti j) :=
    (A.smoothProjectiveFiber j (AbelianProjectivePresentation.CM.presentation A j)).pureBettiSubspace 0 1
  change S.map (BettiComparison.CM.coefficientMap A j) ≤ B ↔ S ≤ (Constructed.Comap.CM.hodge A j).antiholomorphic
  rw [Constructed.Comap.CM.antiholomorphic_comap]
  exact Submodule.map_le_iff_le_comap

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ProjectorTransport.CM

import Mathlib
import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType

/-! # Extreme Slopes -/

namespace OAI.NumberTheory.PadicHodge.ExtremeSlopes.CM.Construction

noncomputable section

/-!
# ExtremeSlopes: extreme slopes force pure Hodge type

This proves the numerical formulation in Statements/ExtremeSlopes.lean, with
explicit submodule-to-sort coercions required for its dimension expressions.
The statement specifications are neither changed nor imported as facts.

Named specialized inputs:
* GaloisValuation: the initial valuation is ±3/2, and conjugated valuations follow
 the odd sign rule. Since d(τ⁻¹) = v(τ), the slope depends only on res χ.
* FrobeniusSlope: the Newton number is dimension times (1/2 - valuation/3).
 This is the numerical Newton hypothesis already present in the target.
* GeometricComparison: Frobenius commutes with the filtration-preserving projectors;
 the paired realizations have equal total and filtered dimensions.
* WeakAdmissibility/GeometricComparison: ambient weak admissibility, with tH ≤ tN on every stable
 subspace. WeakAdmissibility is not independently needed once GeometricComparison supplies this.
* HodgeDecomposition: the complementary weight-one pieces, carried by the existing
 WeightOneHodgeStructure; the filtered comparison identifies Fil¹ with
 the holomorphic piece. Complex projectors preserve both pieces.

The proof derives equality on each projector summand from inequalities
on its image and kernel, Newton additivity, and the total equality.
No equality on a summand and no pure Hodge type is assumed.

The target's existing modeling boundary is retained: the identification
of F1, N, and the paired projectors with geometric cohomology is an input.
GeometricComparison and WeakAdmissibility still contain undefined proposed geometric interfaces, so
this file takes their specialized numerical clauses explicitly instead
of pretending those schemas are elaborated theorems. No additional
substantive assumptions are introduced. The normalization hv and complex
projector idempotence hPC are retained for agreement with the target but
are unnecessary for this implication.
-/

open scoped TensorProduct
open OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField

/--
Numerical weak admissibility for the weight-one filtration
Fil⁰ = D, Fil¹ = F1, Fil² = 0.

N is the Newton-number function, normalized using dimensions over K.
Its identification with Frobenius determinant valuations is an input
from the filtered-Frobenius comparison theory.
-/
def WeaklyAdmissible01
    {K D : Type*} [Field K]
    [AddCommGroup D] [Module K D] [FiniteDimensional K D]
    (F1 : Submodule K D) (φ : Module.End K D)
    (N : Submodule K D → ℚ) : Prop :=
  (Module.finrank K F1 : ℚ) = N ⊤ ∧
  ∀ S : Submodule K D,
    (∀ x ∈ S, φ x ∈ S) →
      (Module.finrank K ↥(S ⊓ F1) : ℚ) ≤ N S

/-- A filtration-preserving projector splits the first filtration step. -/
lemma filtered_projector_finrank
    {K D : Type*} [Field K] [AddCommGroup D] [Module K D]
    [FiniteDimensional K D]
    (F : Submodule K D) (P : Module.End K D)
    (hP : P.comp P = P) (hF : ∀ x ∈ F, P x ∈ F) :
    Module.finrank K ↥(LinearMap.range P ⊓ F) +
      Module.finrank K ↥(LinearMap.ker P ⊓ F) = Module.finrank K F := by
  have hc : IsCompl (LinearMap.range P) (LinearMap.ker P) :=
    LinearMap.IsIdempotentElem.isCompl (show IsIdempotentElem P from hP)
  have hs : (LinearMap.range P ⊓ F) ⊔ (LinearMap.ker P ⊓ F) = F := by
    apply le_antisymm (sup_le inf_le_right inf_le_right)
    intro x hx
    apply Submodule.mem_sup.mpr
    refine ⟨P x, ⟨⟨x, rfl⟩, hF x hx⟩, x - P x, ⟨?_, F.sub_mem hx (hF x hx)⟩, ?_⟩
    · change P (x - P x) = 0
      have hid : P (P x) = P x := LinearMap.congr_fun hP x
      rw [map_sub, hid, sub_self]
    · simp
  have hi : (LinearMap.range P ⊓ F) ⊓ (LinearMap.ker P ⊓ F) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    exact hc.disjoint.le_bot ⟨hx.1.1, hx.2.1⟩
  have hd := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range P ⊓ F) (LinearMap.ker P ⊓ F)
  rw [hs, hi] at hd
  simpa only [finrank_bot, add_zero] using hd.symm

/-- Weak admissibility and additivity force equality on a projector summand. -/
lemma newton_eq_hodge_on_projector
    {K D : Type*} [Field K] [AddCommGroup D] [Module K D]
    [FiniteDimensional K D]
    (F : Submodule K D) (φ P : Module.End K D)
    (N : Submodule K D → ℚ)
    (h_WeakAdmissibility : WeaklyAdmissible01 F φ N)
    (hP : P.comp P = P) (hcomm : P.comp φ = φ.comp P)
    (hF : ∀ x ∈ F, P x ∈ F)
    (hN : N (LinearMap.range P) + N (LinearMap.ker P) = N ⊤) :
    (Module.finrank K ↥(LinearMap.range P ⊓ F) : ℚ) = N (LinearMap.range P) := by
  have hr := h_WeakAdmissibility.2 (LinearMap.range P) (by
    rintro x ⟨y, rfl⟩
    exact ⟨φ y, LinearMap.congr_fun hcomm y⟩)
  have hk := h_WeakAdmissibility.2 (LinearMap.ker P) (by
    intro x hx
    change P (φ x) = 0
    change P x = 0 at hx
    have he := LinearMap.congr_fun hcomm x
    change P (φ x) = φ (P x) at he
    rw [he, hx, map_zero])
  have hd : (Module.finrank K ↥(LinearMap.range P ⊓ F) : ℚ) +
      (Module.finrank K ↥(LinearMap.ker P ⊓ F) : ℚ) = Module.finrank K F := by
    exact_mod_cast filtered_projector_finrank F P hP hF
  have ht := h_WeakAdmissibility.1
  linarith

/-- A graded image with no holomorphic vectors is antiholomorphic. -/
lemma range_le_right_of_inf_eq_bot
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A B : Submodule K V) (hAB : IsCompl A B)
    (P : Module.End K V)
    (hA : ∀ x ∈ A, P x ∈ A) (hB : ∀ x ∈ B, P x ∈ B)
    (hz : LinearMap.range P ⊓ A = ⊥) : LinearMap.range P ≤ B := by
  rintro z ⟨x, rfl⟩
  have hx : x ∈ A ⊔ B := by rw [hAB.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  have hpa : P a = 0 := by
    have hm : P a ∈ LinearMap.range P ⊓ A := ⟨⟨a, rfl⟩, hA a ha⟩
    rw [hz] at hm
    exact hm
  rw [← hab, map_add, hpa, zero_add]
  exact hB b hb

/-- Endpoint Hodge numbers determine both pure types of a nonzero graded image. -/
lemma pure_type_of_extreme_number
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (A B : Submodule K V) (h_HodgeDecomposition : IsCompl A B)
    (P : Module.End K V)
    (hA : ∀ x ∈ A, P x ∈ A) (hB : ∀ x ∈ B, P x ∈ B)
    (hne : LinearMap.range P ≠ ⊥)
    (slope : ℚ) (hext : slope = 0 ∨ slope = 1)
    (hd : (Module.finrank K ↥(LinearMap.range P ⊓ A) : ℚ) =
      (Module.finrank K ↥(LinearMap.range P) : ℚ) * slope) :
    (slope = 1 ↔ LinearMap.range P ≤ A) ∧
    (slope = 0 ↔ LinearMap.range P ≤ B) := by
  have hnot : ¬ (LinearMap.range P ≤ A ∧ LinearMap.range P ≤ B) := by
    rintro ⟨ha, hb⟩
    apply hne
    exact le_antisymm ((le_inf ha hb).trans h_HodgeDecomposition.inf_eq_bot.le) bot_le
  have h1 : slope = 1 → LinearMap.range P ≤ A := by
    intro hs
    rw [hs, mul_one] at hd
    have heq : LinearMap.range P ⊓ A = LinearMap.range P :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by exact_mod_cast hd)
    exact heq.symm.le.trans inf_le_right
  have h0 : slope = 0 → LinearMap.range P ≤ B := by
    intro hs
    rw [hs, mul_zero] at hd
    have hz : LinearMap.range P ⊓ A = ⊥ :=
      Submodule.finrank_eq_zero.mp (by exact_mod_cast hd)
    exact range_le_right_of_inf_eq_bot A B h_HodgeDecomposition P hA hB hz
  refine ⟨⟨h1, ?_⟩, ⟨h0, ?_⟩⟩
  · intro ha
    rcases hext with hs | hs
    · exact False.elim (hnot ⟨ha, h0 hs⟩)
    · exact hs
  · intro hb
    rcases hext with hs | hs
    · exact hs
    · exact False.elim (hnot ⟨h1 hs, hb⟩)

/-- ExtremeSlopes: extreme slopes determine pure Hodge type uniformly
over full extensions of the projective parameter. -/
theorem extreme_slopes_force_pure_hodge_type
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : AlgebraicGeometry.ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun τ : Gal(E/ℚ) => AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (_hv : v.val 1 = true)
    (s : ℚ)
    (h_GaloisValuation_extreme : s = -3 / 2 ∨ s = 3 / 2)

    -- X indexes occurring full parameter extensions and their conjugates.
    -- res records the restriction of the conjugating automorphism to E.
    (X : Type*) (res : X → Gal(E/ℚ))

    (q : ℕ) [Fact q.Prime]
    (L D₀ : Type*)
    [Field L] [Algebra ℚ_[q] L] [FiniteDimensional ℚ_[q] L]
    [AddCommGroup D₀] [Module ℚ_[q] D₀]
    [FiniteDimensional ℚ_[q] D₀]
    (φ₀ : Module.End ℚ_[q] D₀)

    -- The added coefficient factor has identity Frobenius:
    -- φ₀.baseChange L acts as a ⊗ x ↦ a ⊗ φ₀ x.
    (F1 : Submodule L (L ⊗[ℚ_[q]] D₀))
    (N : Submodule L (L ⊗[ℚ_[q]] D₀) → ℚ)
    (h_WeakAdmissibility_GeometricComparison_WA : WeaklyAdmissible01 F1 (φ₀.baseChange L) N)

    -- Hecke projectors on the filtered Frobenius realization.
    (Pq : X → Module.End L (L ⊗[ℚ_[q]] D₀))
    (hPq : ∀ χ, (Pq χ).comp (Pq χ) = Pq χ)
    (h_GeometricComparison_comm : ∀ χ,
      (Pq χ).comp (φ₀.baseChange L) =
        (φ₀.baseChange L).comp (Pq χ))
    (h_GeometricComparison_Fil : ∀ χ x, x ∈ F1 → Pq χ x ∈ F1)
    (hNadd : ∀ χ,
      N (LinearMap.range (Pq χ)) +
        N (LinearMap.ker (Pq χ)) = N ⊤)

    -- Equations (6) and (9), using d(τ⁻¹) = v(τ).
    -- This expression depends only on res χ.
    (h_FrobeniusSlope_GaloisValuation_Newton : ∀ χ,
      N (LinearMap.range (Pq χ)) =
        (Module.finrank L ↥(LinearMap.range (Pq χ)) : ℚ) *
          (1 / 2 - (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val (res χ)) : ℚ) * s / 3))

    (U : Type*) [AddCommGroup U] [Module ℚ U]
    [FiniteDimensional ℚ U]
    (H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U)

    -- Corresponding complex Hecke projectors preserve both Hodge pieces.
    (PC : X → Module.End ℂ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U))
    (_hPC : ∀ χ, (PC χ).comp (PC χ) = PC χ)
    (h10 : ∀ χ x,
      x ∈ H.holomorphic → PC χ x ∈ H.holomorphic)
    (h01 : ∀ χ x,
      x ∈ H.antiholomorphic → PC χ x ∈ H.antiholomorphic)
    (hne : ∀ χ, LinearMap.range (PC χ) ≠ ⊥)

    -- Comparison of total and filtered dimensions.
    (h_GeometricComparison_dim : ∀ χ,
      Module.finrank L ↥(LinearMap.range (Pq χ)) =
        Module.finrank ℂ ↥(LinearMap.range (PC χ)))
    (h_GeometricComparison_HodgeDecomposition_filteredDim : ∀ χ,
      Module.finrank L ↥(LinearMap.range (Pq χ) ⊓ F1) =
        Module.finrank ℂ
          ↥(LinearMap.range (PC χ) ⊓ H.holomorphic)) :
    ∀ χ : X,
      let slope : ℚ :=
        1 / 2 - (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val (res χ)) : ℚ) * s / 3
      (slope = 0 ∨ slope = 1) ∧
      (slope = 1 ↔
        LinearMap.range (PC χ) ≤ H.holomorphic) ∧
      (slope = 0 ↔
        LinearMap.range (PC χ) ≤ H.antiholomorphic) := by
  intro χ
  let slope : ℚ :=
    1 / 2 - (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val (res χ)) : ℚ) * s / 3
  have hext : slope = 0 ∨ slope = 1 := by
    rcases h_GaloisValuation_extreme with hs | hs <;>
      cases hb : v.val (res χ) <;> norm_num [slope, AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue, hb, hs]
  have heq := newton_eq_hodge_on_projector F1 (φ₀.baseChange L) (Pq χ) N
    h_WeakAdmissibility_GeometricComparison_WA (hPq χ) (h_GeometricComparison_comm χ) (h_GeometricComparison_Fil χ) (hNadd χ)
  rw [h_FrobeniusSlope_GaloisValuation_Newton χ, h_GeometricComparison_dim χ, h_GeometricComparison_HodgeDecomposition_filteredDim χ] at heq
  exact ⟨hext, pure_type_of_extreme_number H.holomorphic H.antiholomorphic
    H.complementary (PC χ) (h10 χ) (h01 χ) (hne χ) slope hext heq⟩

/-- The same conclusion with separate named valuation and slope inputs. -/
theorem extreme_slopes_of_named_inputs
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : AlgebraicGeometry.ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun τ : Gal(E/ℚ) => AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (_hv : v.val 1 = true)
    (s : ℚ)

    -- X indexes occurring full parameter extensions and their conjugates.
    -- res records the restriction of the conjugating automorphism to E.
    (X : Type*) (res : X → Gal(E/ℚ))
    (valuation : X → ℚ)
    (h_GaloisValuation : (s = -3 / 2 ∨ s = 3 / 2) ∧
      ∀ χ, valuation χ = (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val (res χ)) : ℚ) * s)

    (q : ℕ) [Fact q.Prime]
    (L D₀ : Type*)
    [Field L] [Algebra ℚ_[q] L] [FiniteDimensional ℚ_[q] L]
    [AddCommGroup D₀] [Module ℚ_[q] D₀]
    [FiniteDimensional ℚ_[q] D₀]
    (φ₀ : Module.End ℚ_[q] D₀)

    -- The added coefficient factor has identity Frobenius:
    -- φ₀.baseChange L acts as a ⊗ x ↦ a ⊗ φ₀ x.
    (F1 : Submodule L (L ⊗[ℚ_[q]] D₀))
    (N : Submodule L (L ⊗[ℚ_[q]] D₀) → ℚ)
    (h_WeakAdmissibility_GeometricComparison_WA : WeaklyAdmissible01 F1 (φ₀.baseChange L) N)

    -- Hecke projectors on the filtered Frobenius realization.
    (Pq : X → Module.End L (L ⊗[ℚ_[q]] D₀))
    (hPq : ∀ χ, (Pq χ).comp (Pq χ) = Pq χ)
    (h_GeometricComparison_comm : ∀ χ,
      (Pq χ).comp (φ₀.baseChange L) =
        (φ₀.baseChange L).comp (Pq χ))
    (h_GeometricComparison_Fil : ∀ χ x, x ∈ F1 → Pq χ x ∈ F1)
    (hNadd : ∀ χ,
      N (LinearMap.range (Pq χ)) +
        N (LinearMap.ker (Pq χ)) = N ⊤)

    -- FrobeniusSlope's Newton formula before substituting the GaloisValuation sign rule.
    (h_FrobeniusSlope : ∀ χ,
      N (LinearMap.range (Pq χ)) =
        (Module.finrank L ↥(LinearMap.range (Pq χ)) : ℚ) *
          (1 / 2 - valuation χ / 3))

    (U : Type*) [AddCommGroup U] [Module ℚ U]
    [FiniteDimensional ℚ U]
    (H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U)

    -- Corresponding complex Hecke projectors preserve both Hodge pieces.
    (PC : X → Module.End ℂ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U))
    (_hPC : ∀ χ, (PC χ).comp (PC χ) = PC χ)
    (h10 : ∀ χ x,
      x ∈ H.holomorphic → PC χ x ∈ H.holomorphic)
    (h01 : ∀ χ x,
      x ∈ H.antiholomorphic → PC χ x ∈ H.antiholomorphic)
    (hne : ∀ χ, LinearMap.range (PC χ) ≠ ⊥)

    -- Comparison of total and filtered dimensions.
    (h_GeometricComparison_dim : ∀ χ,
      Module.finrank L ↥(LinearMap.range (Pq χ)) =
        Module.finrank ℂ ↥(LinearMap.range (PC χ)))
    (h_GeometricComparison_HodgeDecomposition_filteredDim : ∀ χ,
      Module.finrank L ↥(LinearMap.range (Pq χ) ⊓ F1) =
        Module.finrank ℂ
          ↥(LinearMap.range (PC χ) ⊓ H.holomorphic)) :
    ∀ χ : X,
      let slope : ℚ :=
        1 / 2 - (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val (res χ)) : ℚ) * s / 3
      (slope = 0 ∨ slope = 1) ∧
      (slope = 1 ↔
        LinearMap.range (PC χ) ≤ H.holomorphic) ∧
      (slope = 0 ↔
        LinearMap.range (PC χ) ≤ H.antiholomorphic) := by
  apply extreme_slopes_force_pure_hodge_type E v _hv s h_GaloisValuation.1 X res
    q L D₀ φ₀ F1 N h_WeakAdmissibility_GeometricComparison_WA Pq hPq h_GeometricComparison_comm h_GeometricComparison_Fil hNadd
    (fun χ => (h_FrobeniusSlope χ).trans (by rw [h_GaloisValuation.2 χ]))
    U H PC _hPC h10 h01 hne h_GeometricComparison_dim h_GeometricComparison_HodgeDecomposition_filteredDim

end

end OAI.NumberTheory.PadicHodge.ExtremeSlopes.CM.Construction

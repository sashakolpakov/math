import OAI.Analysis.HodgeTheory.Decomposition.Dolbeault

/-! # Correction -/

namespace OAI.Analysis.HodgeTheory.Decomposition.Correction.Constructions

noncomputable section

/-! The explicit correction step for closed filtered representatives.
The input is an actual pure primitive and its derivative identity, not a
cohomological decomposition assumption. The full HodgeDecomposition theorem uses the smooth
harmonic representative construction to prove the filtration equality. -/

open scoped BigOperators

variable (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- The actual exterior derivative bundled as a closed form. -/
def derivativeClosed (n : ℕ) (form : X.componentForms n) : X.componentClosedForms (n + 1) :=
  ⟨X.componentExteriorDerivative n form, X.componentExteriorDerivative_squared n form⟩

theorem derivativeClosed_class_zero (n : ℕ) (form : X.componentForms n) :
    X.componentDeRhamClass (n + 1) (derivativeClosed X n form) = 0 := by
  rw [X.componentDeRhamClass_eq_zero_iff]
  exact ⟨form, rfl⟩

theorem derivativeClosed_betti_zero (n : ℕ) (form : X.componentForms n) :
    X.closedFormBettiClass (n + 1) (derivativeClosed X n form) = 0 := by
  change X.deRhamBettiEquiv (n + 1)
    (X.componentDeRhamClass (n + 1) (derivativeClosed X n form)) = 0
  rw [derivativeClosed_class_zero, map_zero]

def topBidegree (n : ℕ) : Core.Constructions.Bidegree n := ⟨(n, 0), Nat.add_zero n⟩

/-- The last nonzero filtration step consists of a single pure type. -/
theorem filteredForms_top_degree (n : ℕ) :
    Core.Constructions.filteredForms X n (n : ℤ) = Core.Constructions.pureFormsAt X n (topBidegree n) := by
  apply le_antisymm
  · intro form hform
    rw [← Projectors.Constructions.sum_componentProjection X n form]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i = topBidegree n
    · subst i
      exact Projectors.Constructions.componentProjection_pure X n (topBidegree n) form
    · have hneq : i.val.1 ≠ n := fun he => hi (Dolbeault.Constructions.bidegree_eq_of_first i (topBidegree n) he)
      have hn := i.property
      have hlt : (i.val.1 : ℤ) < n := by omega
      rw [Dolbeault.Constructions.projection_below_filtration X n n form hform i hlt]
      exact Submodule.zero_mem _
  · exact le_iSup_of_le (topBidegree n) (le_iSup_of_le (le_refl (n : ℤ)) le_rfl)

/-- Consequently the highest filtration step already has the required cohomological formula. -/
theorem deRhamFiltration_top_degree (n : ℕ) :
    Core.Constructions.deRhamFiltrationBetti X n (n : ℤ) = Core.Constructions.hodgePiece X n (topBidegree n) := by
  rw [Core.Constructions.hodgePiece_eq_image]
  unfold Core.Constructions.deRhamFiltrationBetti
  rw [filteredForms_top_degree]

/-- An explicit pure primitive removes the obstruction, leaving a closed lowest
component and a closed representative one step higher in the filtration. -/
theorem filtered_correction_of_primitive (p q : ℕ)
    (form : X.componentClosedForms (p + (q + 1)))
    (hform : form.val ∈ Core.Constructions.filteredForms X (p + (q + 1)) (p : ℤ))
    (primitive : X.componentPureForms p q)
    (hprimitive :
      X.componentExteriorDerivative (p + (q + 1))
        (Projectors.Constructions.componentProjection X (p + (q + 1)) ⟨(p, q + 1), rfl⟩ form.val) =
      X.componentExteriorDerivative (p + (q + 1)) (Dolbeault.Constructions.componentDDoublePrime X p q primitive).val) :
    ∃ a b : X.componentClosedForms (p + (q + 1)),
      a.val ∈ Core.Constructions.pureFormsAt X (p + (q + 1)) ⟨(p, q + 1), rfl⟩ ∧
      b.val ∈ Core.Constructions.filteredForms X (p + (q + 1)) ((p : ℤ) + 1) ∧
      X.closedFormBettiClass (p + (q + 1)) form =
        X.closedFormBettiClass (p + (q + 1)) a + X.closedFormBettiClass (p + (q + 1)) b := by
  let i : Core.Constructions.Bidegree (p + (q + 1)) := ⟨(p, q + 1), rfl⟩
  let low := Projectors.Constructions.componentProjection X (p + (q + 1)) i form.val
  let anti := (Dolbeault.Constructions.componentDDoublePrime X p q primitive).val
  let prime := Dolbeault.Constructions.componentCast X (by omega : (p + 1) + q = p + (q + 1))
    (Dolbeault.Constructions.componentDPrime X p q primitive).val
  have hlow : X.componentExteriorDerivative (p + (q + 1)) (low - anti) = 0 := by
    rw [map_sub, hprimitive, sub_self]
  let a : X.componentClosedForms (p + (q + 1)) := ⟨low - anti, hlow⟩
  let b := form - a - derivativeClosed X (p + q) primitive.val
  refine ⟨a, b, ?_, ?_, ?_⟩
  · exact (Core.Constructions.pureFormsAt X (p + (q + 1)) i).sub_mem
      (Projectors.Constructions.componentProjection_pure X (p + (q + 1)) i form.val)
      (Dolbeault.Constructions.componentDDoublePrime X p q primitive).property
  · have hraw : b.val = (form.val - low) - prime := by
      change form.val - (low - anti) - X.componentExteriorDerivative (p + q) primitive.val = _
      have hd := Dolbeault.Constructions.componentDolbeault_sum X p q primitive
      change prime + anti = X.componentExteriorDerivative (p + q) primitive.val at hd
      rw [← hd]
      abel
    rw [hraw]
    apply Submodule.sub_mem
    · exact Dolbeault.Constructions.subtract_lowest_projection_filtered X (p + (q + 1)) i form.val hform
    · have hpure := Dolbeault.Constructions.componentCast_pure X (p + 1) q (p + (q + 1))
        (by omega) (Dolbeault.Constructions.componentDPrime X p q primitive)
      apply Submodule.mem_iSup_of_mem (⟨(p + 1, q), by omega⟩ : Core.Constructions.Bidegree (p + (q + 1)))
      apply Submodule.mem_iSup_of_mem (show (p : ℤ) + 1 ≤ ((p + 1 : ℕ) : ℤ) by simp)
      exact hpure
  · change X.closedFormBettiClass (p + (q + 1)) form =
      X.closedFormBettiClass (p + (q + 1)) a +
        X.closedFormBettiClass (p + (q + 1)) (form - a - derivativeClosed X (p + q) primitive.val)
    rw [map_sub, map_sub]
    have hz : X.closedFormBettiClass (p + (q + 1))
        (derivativeClosed X (p + q) primitive.val) = 0 := by
      change X.deRhamBettiEquiv (p + (q + 1))
        (X.componentDeRhamClass (p + (q + 1)) (derivativeClosed X (p + q) primitive.val)) = 0
      have hc : X.componentDeRhamClass (p + (q + 1))
          (derivativeClosed X (p + q) primitive.val) = 0 := by
        rw [X.componentDeRhamClass_eq_zero_iff]
        exact ⟨primitive.val, rfl⟩
      rw [hc, map_zero]
    rw [hz]
    abel

end

end OAI.Analysis.HodgeTheory.Decomposition.Correction.Constructions

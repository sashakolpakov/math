import OAI.AlgebraicTopology.Kunneth.TensorHomologyD

/-! # Single Kunneth Component -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingleKunnethComponent.Constructions

noncomputable section

/-! The actual Künneth component when one factor has homology in a single degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology
open scoped TensorProduct DirectSum

theorem directSum_lof_component_eq {ι : Type} [DecidableEq ι] (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℚ (M i)] (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → Subsingleton (M i)) (z : ⨁ i, M i) :
    DirectSum.lof ℚ ι M i₀ (DirectSum.component ℚ ι M i₀ z) = z := by
  classical
  refine DirectSum.induction_on z ?_ (fun i x => ?_) (fun a b ha hb => ?_)
  · rw [map_zero, map_zero]
  · change DirectSum.lof ℚ ι M i₀
      (DirectSum.component ℚ ι M i₀ (DirectSum.lof ℚ ι M i x)) = DirectSum.lof ℚ ι M i x
    by_cases hi : i = i₀
    · subst i
      rw [DirectSum.component.lof_self]
    · let : Subsingleton (M i) := h i hi
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx, map_zero, map_zero, map_zero]
  · rw [map_add, map_add, ha, hb]

def directSumSingleComponentEquiv {ι : Type} [DecidableEq ι] (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℚ (M i)] (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → Subsingleton (M i)) : M i₀ ≃ₗ[ℚ] (⨁ i, M i) :=
  LinearEquiv.ofBijective (DirectSum.lof ℚ ι M i₀) ⟨
    fun _ _ he => by
      have hc := congrArg (DirectSum.component ℚ ι M i₀) he
      simpa only [DirectSum.component.lof_self] using hc,
    fun z => ⟨DirectSum.component ℚ ι M i₀ z,directSum_lof_component_eq M i₀ h z⟩⟩

variable (C D : ChainComplex (ModuleCat.{0} ℚ) ℕ) (p q : ℕ)
variable (hC : ∀ n, n ≠ p → IsZero (C.homology n))

include hC in
theorem singleKunneth_other_component_zero (ij : AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs (p+q))
    (hij : ij ≠ ⟨(p,q),rfl⟩) :
    Subsingleton (C.homology ij.val.1 ⊗[ℚ] D.homology ij.val.2) := by
  have hi : ij.val.1 ≠ p := by
    intro hi
    have hj : ij.val.2 = q := by have hs := ij.property; omega
    apply hij
    exact Subtype.ext (Prod.ext hi hj)
  let := ModuleCat.subsingleton_of_isZero (hC ij.val.1 hi)
  infer_instance

def algebraicKunnethSingleLeftComponent :
    (C.homology p ⊗[ℚ] D.homology q) ≃ₗ[ℚ] (C⊗D).homology (p+q) :=
  (directSumSingleComponentEquiv
    (fun ij : AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs (p+q) => C.homology ij.val.1 ⊗[ℚ] D.homology ij.val.2)
    ⟨(p,q),rfl⟩ (singleKunneth_other_component_zero C D p q hC)).trans
    (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.algebraicKunneth C D (p+q))

theorem algebraicKunnethSingleLeftComponent_apply (z : C.homology p ⊗[ℚ] D.homology q) :
    algebraicKunnethSingleLeftComponent C D p q hC z =
      AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.algebraicKunneth C D (p+q)
        (DirectSum.lof ℚ (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs (p+q))
          (fun ij => C.homology ij.val.1 ⊗[ℚ] D.homology ij.val.2) ⟨(p,q),rfl⟩ z) := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingleKunnethComponent.Constructions

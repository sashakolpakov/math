import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SelectedSupport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleSupportedCover

/-! # Selected Support Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SelectedSupportCover

noncomputable section

/-! The canonical candidate and the selected local support have the
same image on an actual common global affine Cech cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{0}} [X.IsSeparated] {C : Type} [Preorder C] [HasFiniteProducts C]
  (F₁ F₂ : C ⥤ X.Opens)
  {ι κ₁ ν₁ ρ₁ κ₂ ν₂ ρ₂ μ : Type}
  [LinearOrder ι] [LinearOrder κ₁] [LinearOrder ν₁] [LinearOrder ρ₁]
  [LinearOrder κ₂] [LinearOrder ν₂] [LinearOrder ρ₂] [LinearOrder μ]
  (W : ι → C)
  [∀ (n : ℕ) (z : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ z)) F₁]
  [∀ (n : ℕ) (z : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ z)) F₂]
  (O₁ O₂ : X.Opens) (H : InjectiveIntegerRows.SingleSupportedCandidate.Conditions F₁ F₂ W O₁ O₂)
  (N : X.Modules) [N.IsQuasicoherent] (c : ℕ)
  (B₁ : κ₁ → X.Opens) (J₁ : ν₁ → X.Opens)
  (r₁ : FormalCoproduct.mk ν₁ J₁ ⟶ FormalCoproduct.mk ι (F₁.obj ∘ W))
  (s₁ : FormalCoproduct.mk ν₁ J₁ ⟶ FormalCoproduct.mk κ₁ B₁)
  (B₂ : κ₂ → X.Opens) (J₂ : ν₂ → X.Opens)
  (r₂ : FormalCoproduct.mk ν₂ J₂ ⟶ FormalCoproduct.mk ι (F₂.obj ∘ W))
  (s₂ : FormalCoproduct.mk ν₂ J₂ ⟶ FormalCoproduct.mk κ₂ B₂)
  (V : μ → X.Opens) (hV : ∀ j, IsAffineOpen (V j))
  (T₁ : ρ₁ → X.Opens)
  (l₁ : FormalCoproduct.mk ρ₁ T₁ ⟶ FormalCoproduct.mk (WithBot κ₁)
    (RelativeCech.Intersections.cover (F₁.obj (⊤_ C)) B₁))
  (t₁ : FormalCoproduct.mk ρ₁ T₁ ⟶ FormalCoproduct.mk μ V)
  (T₂ : ρ₂ → X.Opens)
  (l₂ : FormalCoproduct.mk ρ₂ T₂ ⟶ FormalCoproduct.mk (WithBot κ₂)
    (RelativeCech.Intersections.cover (F₂.obj (⊤_ C)) B₂))
  (t₂ : FormalCoproduct.mk ρ₂ T₂ ⟶ FormalCoproduct.mk μ V)
  (hB₁ : ∀ j, B₁ j ≤ O₁) (hB₂ : ∀ j, B₂ j ≤ O₂) (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology (F₁.obj (⊤_ C)) B₁ J₁ s₁
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c) q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T₁ t₁
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c)) q)]
  [IsIso (RelativeCech.Refinement.homology (F₁.obj (⊤_ C)) B₁ J₁ s₁
    (Affine.OrderedInjective.Comparison.integerPresheaf N c) q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T₁ t₁
    (Affine.OrderedInjective.Comparison.integerPresheaf N c)) q)]
  [IsIso (RelativeCech.Refinement.homology (F₂.obj (⊤_ C)) B₂ J₂ s₂
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c) q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T₂ t₂
    (Affine.OrderedInjective.Comparison.sourcePresheaf N c)) q)]
  [IsIso (RelativeCech.Refinement.homology (F₂.obj (⊤_ C)) B₂ J₂ s₂
    (Affine.OrderedInjective.Comparison.integerPresheaf N c) q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T₂ t₂
    (Affine.OrderedInjective.Comparison.integerPresheaf N c)) q)]

include hV hB₁ hB₂ in
theorem comparison :
    H.candidate N c q ≫
      SingleSupportedCover.originalComparison F₁ W N c B₁ J₁ r₁ s₁ V T₁ l₁ t₁ q =
    SingleSupportedCover.originalComparison F₂ W N c B₂ J₂ r₂ s₂ V T₂ l₂ t₂ q := by
  rw [SingleSupportedCover.candidate_global
    F₁ F₂ W O₁ O₂ H N c B₁ J₁ r₁ s₁ V hV T₁ l₁ t₁ hB₁ q,
    H.selectedExtension_eq N c q]
  exact (SingleSupportedCover.comparison
    F₂ F₂ W O₂ O₂ H.selected N c B₂ J₂ r₂ s₂ V hV T₂ l₂ t₂ hB₂ q).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SelectedSupportCover

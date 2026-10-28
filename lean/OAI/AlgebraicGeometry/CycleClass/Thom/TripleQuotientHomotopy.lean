import OAI.AlgebraicGeometry.CycleClass.Thom.TripleChainQuotient
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.QuotientHomotopy

/-! # Triple Quotient Homotopy -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TripleQuotientHomotopy

noncomputable section

/-! Homotopies descend through three factor quotients when their components
annihilate the three actual excluded subcomplexes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex OAI.AlgebraicGeometry.CycleClass.Thom.TripleDegreeQuotient.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.TripleChainQuotient.Constructions

namespace Constructions

variable {k : Type} [Field k]
variable (s t u : ShortComplex (ChainComplex (ModuleCat.{0} k) ℕ))
variable (hs : s.ShortExact) (ht : t.ShortExact) (hu : u.ShortExact)
variable {D : ChainComplex (ModuleCat.{0} k) ℕ}
variable (F G : (s.X₂ ⊗ t.X₂) ⊗ u.X₂ ⟶ D) (H : Homotopy F G)
variable (hF₁ : ((s.f ⊗ₘ 𝟙 t.X₂) ⊗ₘ 𝟙 u.X₂) ≫ F = 0)
variable (hF₂ : ((𝟙 s.X₂ ⊗ₘ t.f) ⊗ₘ 𝟙 u.X₂) ≫ F = 0)
variable (hF₃ : (𝟙 (s.X₂ ⊗ t.X₂) ⊗ₘ u.f) ≫ F = 0)
variable (hG₁ : ((s.f ⊗ₘ 𝟙 t.X₂) ⊗ₘ 𝟙 u.X₂) ≫ G = 0)
variable (hG₂ : ((𝟙 s.X₂ ⊗ₘ t.f) ⊗ₘ 𝟙 u.X₂) ≫ G = 0)
variable (hG₃ : (𝟙 (s.X₂ ⊗ t.X₂) ⊗ₘ u.f) ≫ G = 0)
variable (hH₁ : ∀ a b, ((s.f ⊗ₘ 𝟙 t.X₂) ⊗ₘ 𝟙 u.X₂).f a ≫ H.hom a b = 0)
variable (hH₂ : ∀ a b, ((𝟙 s.X₂ ⊗ₘ t.f) ⊗ₘ 𝟙 u.X₂).f a ≫ H.hom a b = 0)
variable (hH₃ : ∀ a b, (𝟙 (s.X₂ ⊗ t.X₂) ⊗ₘ u.f).f a ≫ H.hom a b = 0)

def tripleQuotientHomotopy :
    Homotopy (TripleChainQuotient.Constructions.tripleChainQuotientDesc s t u hs ht hu F hF₁ hF₂ hF₃)
      (TripleChainQuotient.Constructions.tripleChainQuotientDesc s t u hs ht hu G hG₁ hG₂ hG₃) := by
  let π := (s.g ⊗ₘ t.g) ⊗ₘ u.g
  let : ∀ n, Epi (π.f n) := fun n => TripleChainQuotient.Constructions.tripleQuotient_degree_epi s t u hs ht hu n
  refine HodgeConjecture.DegreeTwo.QuotientHomotopy.Constructions.quotientHomotopyOfComponents π (𝟙 D)
    ((TripleChainQuotient.Constructions.tripleChainQuotientDesc_fac s t u hs ht hu F hF₁ hF₂ hF₃).trans (Category.comp_id F).symm)
    ((TripleChainQuotient.Constructions.tripleChainQuotientDesc_fac s t u hs ht hu G hG₁ hG₂ hG₃).trans (Category.comp_id G).symm)
    H (fun a b => TripleDegreeQuotient.Constructions.tripleDegreeQuotientDesc s t u hs ht hu a (H.hom a b)
      (hH₁ a b) (hH₂ a b) (hH₃ a b)) ?_
  intro a b
  simpa only [HomologicalComplex.id_f, Category.comp_id] using
    TripleDegreeQuotient.Constructions.tripleDegreeQuotientDesc_fac s t u hs ht hu a (H.hom a b) (hH₁ a b) (hH₂ a b) (hH₃ a b)

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TripleQuotientHomotopy

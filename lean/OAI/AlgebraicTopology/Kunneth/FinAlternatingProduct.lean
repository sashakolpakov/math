import OAI.AlgebraicTopology.Kunneth.WedgeAlternating

/-! # Fin Alternating Product -/

namespace OAI.AlgebraicTopology.Kunneth.FinAlternatingProduct

noncomputable section

/-! Alternating products with the degree indexing used by differential forms. -/

set_option backward.isDefEq.respectTransparency false

namespace Constructions

variable {E : Type*} {p q n m : ℕ}

def finBlockProduct (f : (Fin p → E) → ℂ) (g : (Fin q → E) → ℂ)
    (v : Fin (p + q) → E) : ℂ :=
  f (fun i => v (Fin.castAdd q i)) * g (fun i => v (Fin.natAdd p i))

theorem alternatingSum_finBlockProduct (f : (Fin p → E) → ℂ) (g : (Fin q → E) → ℂ)
    (v : Fin (p + q) → E) :
    WedgeAlternating.Constructions.alternatingSum (finBlockProduct f g) v =
      WedgeAlternating.Constructions.alternatingSum (WedgeAlternating.Constructions.blockProduct f g) (v ∘ finSumFinEquiv) :=
  WedgeAlternating.Constructions.alternatingSum_reindex finSumFinEquiv (WedgeAlternating.Constructions.blockProduct f g) v

theorem alternatingSum_finBlock_left (f : (Fin p → E) → ℂ) (g : (Fin q → E) → ℂ)
    (v : Fin (p + q) → E) :
    WedgeAlternating.Constructions.alternatingSum (finBlockProduct (WedgeAlternating.Constructions.alternatingSum f) g) v =
      p.factorial • WedgeAlternating.Constructions.alternatingSum (finBlockProduct f g) v := by
  rw [alternatingSum_finBlockProduct, alternatingSum_finBlockProduct,
    WedgeAlternating.Constructions.alternatingSum_block_left, Fintype.card_fin]

theorem alternatingSum_finBlock_right (f : (Fin p → E) → ℂ) (g : (Fin q → E) → ℂ)
    (v : Fin (p + q) → E) :
    WedgeAlternating.Constructions.alternatingSum (finBlockProduct f (WedgeAlternating.Constructions.alternatingSum g)) v =
      q.factorial • WedgeAlternating.Constructions.alternatingSum (finBlockProduct f g) v := by
  rw [alternatingSum_finBlockProduct, alternatingSum_finBlockProduct,
    WedgeAlternating.Constructions.alternatingSum_block_right, Fintype.card_fin]

theorem alternatingSum_cast (h : n = m) (f : (Fin n → E) → ℂ) (v : Fin m → E) :
    WedgeAlternating.Constructions.alternatingSum (fun w => f (fun i => w (Fin.cast h i))) v =
      WedgeAlternating.Constructions.alternatingSum f (fun i => v (Fin.cast h i)) := by
  subst m
  rfl

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covectorWedge_eq_alternatingSum
    (a : E [⋀^Fin p]→L[ℝ] ℂ) (b : E [⋀^Fin q]→L[ℝ] ℂ)
    (v : Fin (p + q) → E) :
    CovectorWedge.Constructions.covectorWedge a b v = (((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹) •
      WedgeAlternating.Constructions.alternatingSum (finBlockProduct a b) v := by
  rw [CovectorWedge.Constructions.covectorWedge_apply]
  rfl

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.FinAlternatingProduct

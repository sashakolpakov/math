import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.CoverExpansion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReversedModuleCech

/-! # Top Linear Cover Expansion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.TopLinearCoverExpansion.ProjectiveCech

noncomputable section

/-! A homogeneous linear chart can be adjoined as the last coordinate without changing augmented Čech exactness. -/

open _root_.MvPolynomial DirectSum

universe u v w

variable {σ : Type u} [Fintype σ] [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable [Algebra (MvPolynomial (WithTop σ) R) (MvPolynomial σ R)]
  [IsScalarTower R (MvPolynomial (WithTop σ) R) (MvPolynomial σ R)]
variable (he : ∀ i : σ, algebraMap (MvPolynomial (WithTop σ) R) (MvPolynomial σ R) (X (i : WithTop σ)) = X i)
variable (M : Type w) [AddCommGroup M] [Module R M]
  [Module (MvPolynomial (WithTop σ) R) M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial (WithTop σ) R) M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial (WithTop σ) R) (MvPolynomial σ R) M]
variable (l : MvPolynomial σ R)
variable (hl : algebraMap (MvPolynomial (WithTop σ) R) (MvPolynomial σ R) (X ⊤) = l)
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := WithTop σ) R) ℳ]

local instance : Algebra (MvPolynomial (WithBot σᵒᵈ) R) (MvPolynomial σᵒᵈ R) :=
  ‹Algebra (MvPolynomial (WithTop σ) R) (MvPolynomial σ R)›
local instance : IsScalarTower R (MvPolynomial (WithBot σᵒᵈ) R) (MvPolynomial σᵒᵈ R) :=
  ‹IsScalarTower R (MvPolynomial (WithTop σ) R) (MvPolynomial σ R)›
local instance : Module (MvPolynomial σᵒᵈ R) M := ‹Module (MvPolynomial σ R) M›
local instance : Module (MvPolynomial (WithBot σᵒᵈ) R) M := ‹Module (MvPolynomial (WithTop σ) R) M›
local instance : IsScalarTower R (MvPolynomial σᵒᵈ R) M := ‹IsScalarTower R (MvPolynomial σ R) M›
local instance : IsScalarTower R (MvPolynomial (WithBot σᵒᵈ) R) M := ‹IsScalarTower R (MvPolynomial (WithTop σ) R) M›
local instance : IsScalarTower (MvPolynomial (WithBot σᵒᵈ) R) (MvPolynomial σᵒᵈ R) M :=
  ‹IsScalarTower (MvPolynomial (WithTop σ) R) (MvPolynomial σ R) M›
local instance : SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σᵒᵈ) R) ℳ :=
  ‹SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ›
local instance : SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := WithBot σᵒᵈ) R) ℳ :=
  ‹SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := WithTop σ) R) ℳ›

include he hl in
theorem topLinearCoverExpansion_moduleCechExactAt_iff (hlhom : l.IsHomogeneous 1) (d : ℤ) (q : ℕ) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := WithTop σ) R M ℳ d q ↔ Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q := by
  have he' : ∀ i : σᵒᵈ, algebraMap (MvPolynomial (WithBot σᵒᵈ) R) (MvPolynomial σᵒᵈ R)
      (X (i : WithBot σᵒᵈ)) = X i := he
  have hl' : algebraMap (MvPolynomial (WithBot σᵒᵈ) R) (MvPolynomial σᵒᵈ R) (X ⊥) = l := hl
  have h := Linear.CoverExpansion.ProjectiveCech.linearCoverExpansion_moduleCechExactAt_iff (σ := σᵒᵈ) R he' M l hl' ℳ hlhom d q
  have ht := (ReversedModuleCech.ProjectiveCech.moduleCechExactAt_orderDual_iff (σ := WithBot σᵒᵈ) R M ℳ d q).trans
    (h.trans (ReversedModuleCech.ProjectiveCech.moduleCechExactAt_orderDual_iff (σ := σ) R M ℳ d q))
  have horder : OrderDual.instLinearOrder (WithBot σᵒᵈ) =
      (inferInstance : LinearOrder (WithTop σ)) := by
    apply LinearOrder.ext
    intro a b
    change WithBot.LE (α := σᵒᵈ) b a ↔ WithTop.LE (α := σ) a b
    constructor
    · intro hab
      cases hab with
      | bot_le => exact WithTop.LE.le_top (α := σ) _
      | coe_le_coe h => exact WithTop.LE.coe_le_coe h
    · intro hab
      cases hab with
      | le_top => exact WithBot.LE.bot_le (α := σᵒᵈ) _
      | coe_le_coe h => exact WithBot.LE.coe_le_coe h
  rw [horder] at ht
  exact ht

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.TopLinearCoverExpansion.ProjectiveCech

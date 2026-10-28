import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Action
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks

/-! # PEL Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELAction.Construction

noncomputable section

/-!
The action constructed by quotient descent uses precisely ReferenceFamily's concrete
integral-action data. This adapter preserves the underlying scheme maps
and all ring laws; no descended PEL action is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v

variable {S : Scheme.{u}} {g : ℕ} {R : Type v} [CommRing R]

def integralActionEquiv (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) :
    AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A ≃ Action.Construction.EndomorphismAction (A := A.scheme) R where
  toFun ρ := {
    map := ρ.map
    preservesGroup := ρ.preservesGroup
    map_zero := ρ.map_zero
    map_one := ρ.map_one
    map_add := ρ.map_add
    map_mul := ρ.map_mul }
  invFun ρ := {
    map := ρ.map
    preservesGroup := ρ.preservesGroup
    map_zero := ρ.map_zero
    map_one := ρ.map_one
    map_add := ρ.map_add
    map_mul := ρ.map_mul }
  left_inv _ := rfl
  right_inv _ := rfl

/-- FiniteDescent's finite flat quotient carries a unique ReferenceFamily integral action
when the chosen kernel is stable under the source action. -/
theorem quotient_integral_action
    (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A)
    (H : Over S) (i : H ⟶ A.scheme)
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
    (hkernel : i ≫ f.hom = 1)
    (h_FiniteDescent : Descent.Construction.QuotientUniversalProperty i f.hom)
    (hstable : ∀ r, i ≫ ρ.map r ≫ f.hom = 1) :
    ∃! σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R B,
      ∀ r, f.hom ≫ σ.map r = ρ.map r ≫ f.hom := by
  have : EffectiveEpi (f.hom ⊗ₘ f.hom) :=
    Picard.PoincareBundle.Epi.Construction.effectiveEpi_tensor_over_of_fpqc f.hom f.hom
  obtain ⟨σ, hσ, hu⟩ := Action.Construction.quotient_ring_action (integralActionEquiv A ρ)
    i f.hom hkernel h_FiniteDescent hstable
  refine ⟨(integralActionEquiv B).symm σ, hσ, ?_⟩
  intro τ hτ
  apply (integralActionEquiv B).injective
  rw [Equiv.apply_symm_apply]
  exact hu (integralActionEquiv B τ) hτ

/-- Forget only the fixed relative dimension when invoking FiniteDescent's
concrete abelian-scheme proposition. The underlying group is unchanged. -/
def abelianSchemeForgetDimension (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) :
    Picard.PoincareBundle.Epi.Construction.AbelianScheme S where
  toOver := A.scheme
  group := A.group
  commutative := A.commutative
  smooth := inferInstance
  proper := A.proper
  geometricallyConnected := A.connected

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELAction.Construction

import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieEquations
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieFiniteness

/-! # Lie Ranks -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRanks

noncomputable section

/-! ReferenceFamily's actual dual-number Lie-rank condition is the dimension of
a finite algebraic kernel over every field, including positive characteristic. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace AlgebraicLie

theorem hasLieRank_iff_finrank
    {k R : Type} [Field k] [CommRing R] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A)
    (τ : R →+* k) (r : ℕ) :
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ τ r ↔ Module.finrank k (LieEigenspaces.AlgebraicLie.eigenspace A ρ τ) = r := by
  rw [LieEigenspaces.AlgebraicLie.hasLieRank_iff_linearEquiv, FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq,
    Module.finrank_fin_fun]
  exact eq_comm

theorem hasLieRank_iff_integral_kernel
    {E k : Type} [Field E] [NumberField E] [Field k] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (τ : NumberField.RingOfIntegers E →+* k) (r : ℕ) :
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ τ r ↔
      Module.finrank k (LinearMap.ker (Integral.LieEquations.AlgebraicLie.integralEigenEquations A ρ τ)) = r := by
  rw [hasLieRank_iff_finrank, Integral.LieEquations.AlgebraicLie.eigenspace_eq_kernel]

end AlgebraicLie

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRanks

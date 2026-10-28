import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteQuadraticLift
import OAI.RepresentationTheory.Hecke.RadialDilation.ContinuousTestFamilies

/-! # Finite Quadratic Stabilization -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteQuadraticStabilization.Realization

noncomputable section

/-! Small finite-adelic quadratic transformations stabilize actual test vectors up to sign. -/

open scoped Classical _root_.Topology _root_.Matrix
open Filter _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem eventually_finiteQuadratic_fixed (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    ∀ᶠ B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf in 𝓝 0, FiniteQuadratic.Realization.finiteQuadratic D B f = f := by
  let F : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf × (ι → Theta.PoissonAutomorphyNormalizationData.AQf) → ℂ :=
    fun p => D.finiteCharacter (QuadraticCommutator.Realization.ringQuadratic p.1 p.2)
  have hF : IsLocallyConstant F := by
    apply (FiniteSchur.Realization.finiteCharacter_locallyConstant D).comp_continuous
    unfold QuadraticCommutator.Realization.ringQuadratic Matrix.mulVec dotProduct
    fun_prop
  have h₀ : ∀ x, F (0, x) = 1 := by
    intro x
    simp [F, QuadraticCommutator.Realization.ringQuadratic]
  filter_upwards [ContinuousTestFamilies.Realization.eventually_compact_phase_one (0 : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf) F hF h₀
    (tsupport f.val) (Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport f)] with B hB
  apply Subtype.ext
  funext x
  rw [FiniteQuadratic.Realization.finiteQuadratic_apply]
  by_cases hx : f.val x = 0
  · rw [hx, mul_zero]
  · rw [show D.finiteCharacter (QuadraticCommutator.Realization.ringQuadratic B x) = 1 from
      hB x (subset_tsupport f.val hx), one_mul]

theorem eventually_finite_upper_sign (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)
    (f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    ∀ᶠ B : Matrix ι ι Theta.PoissonAutomorphyNormalizationData.AQf in 𝓝 0, ∀ (hB : B.IsSymm) (m : MpF),
      D.finite.project m = QuadraticCommutator.Realization.ringUpper B hB →
      ∃ ε : ℂ, ε ^ 2 = 1 ∧ D.finite.action m f = ε • f := by
  filter_upwards [eventually_finiteQuadratic_fixed D f] with B hfix
  intro hB m hm
  obtain ⟨ε, hε, haction⟩ := FiniteQuadraticLift.Realization.every_finite_quadratic_lift D B hB m hm
  exact ⟨ε, hε, (haction f).trans (congrArg (fun h => ε • h) hfix)⟩

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteQuadraticStabilization.Realization

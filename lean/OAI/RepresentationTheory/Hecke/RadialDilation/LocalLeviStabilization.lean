import OAI.RepresentationTheory.Hecke.RadialDilation.LocalTestStabilizers
import OAI.RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanTestSpace

/-! # Local Levi Stabilization -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.LocalLeviStabilization.Realization

noncomputable section

section

/-! Small linear generators fix actual local test functions up to eighth roots of unity. -/

open scoped Classical _root_.Topology
open Filter OAI.RepresentationTheory.Weil.Local.NonarchimedeanTestSpace.Construction

variable (q n : ℕ) [Fact q.Prime]
local instance c410LocalLeviStabilization_localInst1 : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410LocalLeviStabilization_localInst2 : BorelSpace ℚ_[q] := ⟨rfl⟩

theorem local_levi_finite_phase
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition) (hn : 0 < n)
    (ψ : AddChar ℚ_[q] ℂ) (hψ : Continuous (fun x : ℚ_[q] => ψ x))
    (hunit : ∀ x, ‖ψ x‖ = 1) (hnontrivial : ∃ x, ψ x ≠ 1)
    (A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (hdet : ‖(Weil.Local.FunctionsMetaplectic.Construction.determinantUnit ℚ_[q] A).val‖ = 1)
    (hfix : Weil.Local.FunctionsMetaplectic.Construction.substitutionOperator A f.val = f.val)
    (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ) (hg : Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g = Weil.Local.Generators.Construction.leviSymplectic A) :
    ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ g f = ξ • f := by
  obtain ⟨_, _, hgaussian, _, _, m, _, _, hm, _, _, hlinear, _, _, hcover⟩ :=
    hLocalWeil ℚ_[q] (LocalLiftChoice.Realization.padic_not_discrete q) n hn ψ hψ hunit hnontrivial
  let ξ₀ := Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℚ_[q] ψ (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit ℚ_[q] A) / Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex ℚ_[q] ψ 1
  have hξ₀ : ξ₀ ^ 8 = 1 := Weil.Local.Generators.Construction.index_ratio_eighth_power ℚ_[q] ψ _
    (hgaussian _ (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit ℚ_[q] A).ne_zero).2.2 (hgaussian 1 one_ne_zero).2.2
  have hmfix : Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ (m A) f = ξ₀ • f := by
    apply Subtype.ext
    funext x
    rw [hlinear, Haar.Realization.haarModulus_unit_norm_one q (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit ℚ_[q] A) hdet]
    simp only [Real.sqrt_one, inv_one, Complex.ofReal_one, mul_one]
    change ξ₀ * (Weil.Local.FunctionsMetaplectic.Construction.substitutionOperator A f.val) x = ξ₀ * f.val x
    rw [hfix]
  obtain ⟨ε, hε, hεop⟩ := hcover (m A) g ((hm A).trans hg.symm)
  have hε₈ : ε ^ 8 = 1 := by
    calc
      _ = (ε ^ 2) ^ 4 := by rw [← pow_mul]
      _ = 1 := by rw [hε, one_pow]
  refine ⟨ε * ξ₀, ?_, ?_⟩
  · rw [mul_pow, hε₈, hξ₀, mul_one]
  · rw [hεop, hmfix, smul_smul]

theorem eventually_local_levi_finite_phase
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition) (hn : 0 < n)
    (ψ : AddChar ℚ_[q] ℂ) (hψ : Continuous (fun x : ℚ_[q] => ψ x))
    (hunit : ∀ x, ‖ψ x‖ = 1) (hnontrivial : ∃ x, ψ x ≠ 1)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) :
    ∀ᶠ A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n in 𝓝 1,
      ∀ g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ, Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g = Weil.Local.Generators.Construction.leviSymplectic A →
        ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ g f = ξ • f := by
  obtain ⟨hf, hc⟩ := Weil.Local.NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp f.property
  filter_upwards [LocalTestStabilizers.Realization.eventually_substitutionOperator_fixed q n f.val hf hc,
    LocalTestStabilizers.Realization.eventually_determinant_norm_one q n] with A hfix hdet
  exact local_levi_finite_phase q n hLocalWeil hn ψ hψ hunit hnontrivial A f hdet hfix

end

/-! Small quadratic generators fix actual local test vectors up to lift signs. -/

open scoped Classical _root_.Topology
open Filter OAI.RepresentationTheory.Weil.Local.NonarchimedeanTestSpace.Construction

variable (q n : ℕ) [Fact q.Prime]
local instance c410LocalQuadraticStabilization_localInst1 : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410LocalQuadraticStabilization_localInst2 : BorelSpace ℚ_[q] := ⟨rfl⟩

theorem local_quadratic_finite_phase
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition) (hn : 0 < n)
    (ψ : AddChar ℚ_[q] ℂ) (hψ : Continuous (fun x : ℚ_[q] => ψ x))
    (hunit : ∀ x, ‖ψ x‖ = 1) (hnontrivial : ∃ x, ψ x ≠ 1)
    (B : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ_[q] n) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n)
    (hfix : Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B.val f.val = f.val)
    (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ) (hg : Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g = Weil.Local.Generators.Construction.quadraticSymplectic B) :
    ∃ ξ : ℂ, ξ ^ 2 = 1 ∧ Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ g f = ξ • f := by
  obtain ⟨_, _, _, _, _, _, u, _, _, hu, _, _, hquad, _, hcover⟩ :=
    hLocalWeil ℚ_[q] (LocalLiftChoice.Realization.padic_not_discrete q) n hn ψ hψ hunit hnontrivial
  have hufix : Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ (u B) f = f := by
    apply Subtype.ext
    funext x
    rw [hquad]
    exact congrFun hfix x
  obtain ⟨ε, hε, hεop⟩ := hcover (u B) g ((hu B).trans hg.symm)
  exact ⟨ε, hε, (hεop f).trans (congrArg (fun h => ε • h) hufix)⟩

theorem eventually_local_quadratic_finite_phase
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition) (hn : 0 < n)
    (ψ : AddChar ℚ_[q] ℂ) (hψ : Continuous (fun x : ℚ_[q] => ψ x))
    (hunit : ∀ x, ‖ψ x‖ = 1) (hnontrivial : ∃ x, ψ x ≠ 1)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) :
    ∀ᶠ B : Matrix (Fin n) (Fin n) ℚ_[q] in 𝓝 0,
      ∀ (hB : B.IsSymm) (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ),
        Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g = Weil.Local.Generators.Construction.quadraticSymplectic ⟨B, hB⟩ →
        ∃ ξ : ℂ, ξ ^ 2 = 1 ∧ Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ g f = ξ • f := by
  have hc := (Weil.Local.NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp f.property).2
  filter_upwards [LocalTestStabilizers.Realization.eventually_quadraticOperator_fixed q n ψ hψ f.val hc] with B hfix
  intro hB g hg
  exact local_quadratic_finite_phase q n hLocalWeil hn ψ hψ hunit hnontrivial ⟨B, hB⟩ f hfix g hg

end

end OAI.RepresentationTheory.Hecke.RadialDilation.LocalLeviStabilization.Realization

import OAI.RepresentationTheory.Hecke.RadialDilation.LocalBigCellStabilization

/-! # Local Weil Smoothness -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.LocalWeilSmoothness.Realization

noncomputable section

/-! Finite-order projective smoothness of the actual bare p-adic Weil action. -/

open scoped Classical _root_.Topology
open Filter

variable (q n : ℕ) [Fact q.Prime]
local instance c410LocalWeilSmoothness_localInst1 : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410LocalWeilSmoothness_localInst2 : BorelSpace ℚ_[q] := ⟨rfl⟩

theorem eventually_local_weil_finite_phase
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition) (hn : 0 < n)
    (ψ : AddChar ℚ_[q] ℂ) (hψ : Continuous (fun x : ℚ_[q] => ψ x))
    (hunit : ∀ x, ‖ψ x‖ = 1) (hnontrivial : ∃ x, ψ x ≠ 1)
    (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] n) :
    ∀ᶠ s : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n in 𝓝 1,
      ∀ g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ, Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g = s →
        ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ g f = ξ • f := by
  have hparam := LocalBigCellStabilization.Realization.eventually_local_bigCell_finite_phase q n hLocalWeil hn ψ hψ hunit hnontrivial f
  have ht : Tendsto (LocalBigCellStabilization.Realization.localBigCellParameters q n) (𝓝 (LocalBigCellStabilization.Realization.localBigCellOne q n)) (𝓝 (1, (0, 0))) := by
    simpa only [LocalBigCellStabilization.Realization.localBigCellParameters_one] using
      (LocalBigCellStabilization.Realization.localBigCellParameters_continuous q n).tendsto (LocalBigCellStabilization.Realization.localBigCellOne q n)
  have hcell : ∀ᶠ s : LocalBigCellStabilization.Realization.LocalBigCell q n in 𝓝 (LocalBigCellStabilization.Realization.localBigCellOne q n),
      ∀ g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] n ψ, Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] n ψ g = s.val →
        ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] n ψ g f = ξ • f := by
    filter_upwards [ht.eventually hparam] with s hs
    intro g hg
    exact hs (LocalBigCellStabilization.Realization.localBigCell_parameters_symmetric q n s).1 (LocalBigCellStabilization.Realization.localBigCell_parameters_symmetric q n s).2
      g (hg.trans (LocalBigCellStabilization.Realization.localBigCell_factorization q n s))
  have hmap := (LocalBigCellStabilization.Realization.localBigCell_isOpen q n).isOpenEmbedding_subtypeVal.map_nhds_eq (LocalBigCellStabilization.Realization.localBigCellOne q n)
  change Filter.map (Subtype.val : LocalBigCellStabilization.Realization.LocalBigCell q n → Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n)
    (𝓝 (LocalBigCellStabilization.Realization.localBigCellOne q n)) = 𝓝 (1 : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ_[q] n) at hmap
  rw [← hmap]
  exact hcell

end

end OAI.RepresentationTheory.Hecke.RadialDilation.LocalWeilSmoothness.Realization

import OAI.RepresentationTheory.Weil.UnitarySplitting.RealChartTestSpace
import OAI.RepresentationTheory.Weil.UnitarySplitting.LocalTest
import OAI.RepresentationTheory.Weil.Local.Analytic
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier

/-! # Shifted Test Product -/

namespace OAI.RepresentationTheory.Theta.Adelic.ShiftedTestProduct

noncomputable section

/-! Translated products belong to the actual Bruhat test space over any
characteristic-zero local field. -/

open scoped ComplexConjugate

open OAI.RepresentationTheory.Weil.Local.Analytic.Construction

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable {N : ℕ}

theorem shifted_product_mem (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (q : Weil.Local.FunctionsMetaplectic.Construction.Position k N) :
    (fun x => f.val (x - q) * conj (h.val x)) ∈ Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N := by
  by_cases hArch : ∀ n : ℕ, ‖(n : k)‖ ≤ 1
  · let : IsUltrametricDist k :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hArch
    obtain ⟨hfl, hfs⟩ := Weil.UnitarySplitting.UltraMultiplier.Construction.schwartzBruhat_ultra_iff.mp f.property
    obtain ⟨hhl, _⟩ := Weil.UnitarySplitting.UltraMultiplier.Construction.schwartzBruhat_ultra_iff.mp h.property
    apply Weil.Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
    · exact (hfl.comp_continuous (continuous_id.sub continuous_const)).mul (hhl.comp conj)
    · exact (hfs.comp_homeomorph (Homeomorph.subRight q)).mul_right
  · obtain ⟨s, ⟨e⟩⟩ := Weil.UnitarySplitting.LocalTest.Construction.exists_real_coordinates_of_unbounded k hArch N
    obtain ⟨φ, hφ⟩ := (Weil.UnitarySplitting.RealChartTestSpace.Construction.schwartzBruhat_realChart_iff e).mp f.property
    obtain ⟨η, hη⟩ := (Weil.UnitarySplitting.RealChartTestSpace.Construction.schwartzBruhat_realChart_iff e).mp h.property
    let a := SchwartzMap.compSubConstCLM ℝ (e.symm q) φ
    let b := η.postcompCLM Complex.conjCLE.toContinuousLinearMap
    apply (Weil.UnitarySplitting.RealChartTestSpace.Construction.schwartzBruhat_realChart_iff e).mpr
    refine ⟨SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) a b, ?_⟩
    funext x
    rw [hφ, hη]
    change φ (e.symm (x - q)) * conj (η (e.symm x)) =
      φ (e.symm x - e.symm q) * conj (η (e.symm x))
    rw [map_sub]

variable [MeasurableSpace k] [BorelSpace k]

theorem shifted_product_fourier_inversion (hnd : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ x : k, ‖ψ x‖ = 1)
    (hn : ∃ x : k, ψ x ≠ 1) (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (q z : Weil.Local.FunctionsMetaplectic.Construction.Position k N) :
    Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ)
      (Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Weil.Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ) (fun x => f.val (x - q) * conj (h.val x))) (-z) =
        f.val (z - q) * conj (h.val z) := by
  let a : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N := ⟨_, shifted_product_mem f h q⟩
  have hi := (Weil.Local.Analytic.Construction.localField_analytic_normalization hnd ψ hc hu hn N).2.2.2 a (-z)
  simpa only [neg_neg] using hi

end

end OAI.RepresentationTheory.Theta.Adelic.ShiftedTestProduct

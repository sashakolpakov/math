import OAI.Analysis.PDE.Concentration.Lattice.Localized

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter _root_.MeasureTheory OAI.Analysis.PDE.Green
open scoped Topology

theorem real_operator_second_green_lattice_localized
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (K : ι → ι → EuclideanSpace ℝ ι → ℝ) {r u v : EuclideanSpace ℝ ι → ℝ}
    (hK : ∀ i j, ContDiff ℝ 1 (K i j))
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hKs : ∀ i j x, K i j x = K j i x)
    (hdiv : ∀ x j, ∑ i, fderiv ℝ (K i j) x (EuclideanSpace.single i 1) = 0)
    (hreg : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 →
      fderiv ℝ r x ≠ 0 ∨ v =ᶠ[𝓝 x] (fun _ => 0))
    (hzero : ∀ x, r x = 0 → ∑ i, fderiv ℝ r x (EuclideanSpace.single i 1) *
      OAI.Analysis.PDE.Green.secondGreenFlux (fun i => EuclideanSpace.single i 1) K u v i x = 0)
    (hface : CompatibleLatticeFaces c L a b r
      (OAI.Analysis.PDE.Green.secondGreenFlux (fun i => EuclideanSpace.single i 1) K u v)) :
    (∫ x in (euclideanLatticeCell c L a b) ∩ {x | r x < 0}, u x *
      (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ v) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) =
    ∫ x in (euclideanLatticeCell c L a b) ∩ {x | r x < 0}, v x *
      (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
  let d : ι → EuclideanSpace ℝ ι := fun i => EuclideanSpace.single i 1
  have hb := (isBounded_euclideanLatticeCell c L a b).subset
    (inter_subset_left : ((euclideanLatticeCell c L a b) ∩ {x | r x < 0}) ⊆ _)
  have hvF := OAI.Analysis.PDE.Green.contDiff_realFlux d K hK hv
  have huF := OAI.Analysis.PDE.Green.contDiff_realFlux d K hK hu
  have hvi : IntegrableOn (fun x => u x * ∑ i, fderiv ℝ (OAI.Analysis.PDE.Green.realFlux d K v i) x (d i))
      ((euclideanLatticeCell c L a b) ∩ {x | r x < 0}) :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hu.continuous.mul
      (continuous_finsetSum _ (fun i _ => OAI.Analysis.PDE.Green.continuous_directional (hvF i) (d i))))
  have hui : IntegrableOn (fun x => v x * ∑ i, fderiv ℝ (OAI.Analysis.PDE.Green.realFlux d K u i) x (d i))
      ((euclideanLatticeCell c L a b) ∩ {x | r x < 0}) :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hv.continuous.mul
      (continuous_finsetSum _ (fun i _ => OAI.Analysis.PDE.Green.continuous_directional (huF i) (d i))))
  have hreg' : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 →
      fderiv ℝ r x ≠ 0 ∨ ∀ᶠ y in 𝓝 x, ∀ i, OAI.Analysis.PDE.Green.secondGreenFlux d K u v i y = 0 := by
    intro x hx hrx
    rcases hreg x hx hrx with h | h
    · exact Or.inl h
    · exact Or.inr (OAI.Analysis.PDE.Green.secondGreenFlux_eventually_zero d K u v x h)
  have he := integral_divergence_euclidean_lattice_localized c L a b hab
    (OAI.Analysis.PDE.Green.secondGreenFlux d K u v) (OAI.Analysis.PDE.Green.contDiff_secondGreenFlux d K hK hu hv) hr hreg' hzero hface
  change (∫ x in (euclideanLatticeCell c L a b) ∩ {x | r x < 0},
    ∑ i, fderiv ℝ (OAI.Analysis.PDE.Green.secondGreenFlux d K u v i) x (d i)) = 0 at he
  simp_rw [OAI.Analysis.PDE.Green.secondGreenFlux_divergence d K hK hu hv hKs] at he
  rw [integral_sub hvi hui] at he
  have heq := sub_eq_zero.mp he
  simpa only [OAI.Analysis.PDE.Green.realFlux_divergence d K hK hv hdiv,
    OAI.Analysis.PDE.Green.realFlux_divergence d K hK hu hdiv] using heq

end OAI.Analysis.PDE.Concentration

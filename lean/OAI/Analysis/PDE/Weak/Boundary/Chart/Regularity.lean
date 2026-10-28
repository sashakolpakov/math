import OAI.Analysis.PDE.Weak.Boundary.Chart.Equation
import OAI.Analysis.PDE.Weak.Boundary.Chart.LocalEllipticity
import OAI.Analysis.PDE.Weak.Elliptic.BoundaryClassical

noncomputable section
open Set Filter _root_.MeasureTheory InnerProductSpace
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- The genuine weak solution becomes classical up to the flattened
boundary. The original equation need only hold on a neighborhood of the
point, independently of the artificial support boundary of the H¹ pair. -/
theorem chart_weak_solution_classical
    (k : Fin (m+1)) {U V Ω W : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)}
    (hU : IsOpen U) (hV : IsOpen V) (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hUb : Bornology.IsBounded U) (hVb : Bornology.IsBounded V)
    {G P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    (hGU : MapsTo G U V) (hPV : MapsTo P V U)
    (hPG : ∀ y ∈ U, P (G y) = y) (hGP : ∀ z ∈ V, G (P z) = z)
    (hflat : ∀ y ∈ U, G y ∈ Ω ↔ 0 < y k)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ ∞ A) {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ z ∈ V, ∀ v, lam * ‖v‖^2 ≤ inner ℝ (A z v) v)
    (p : H1Pair m) (hp : p ∈ H1Zero (V ∩ Ω))
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (he : WeakDivergenceEquation (W ∩ Ω) (fun z => A z (p.2 z)) g)
    (q : ℕ) (hq : 2 ≤ q) {x : OAI.Analysis.PDE.Variational.CellCoordinates m} (hx : x ∈ U) (hxW : G x ∈ W) :
    ∃ (O : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ),
      IsOpen O ∧ x ∈ O ∧ O ⊆ U ∧ ContDiff ℝ q u ∧
      (∀ᵐ y ∂volume, y ∈ {y | 0 < y k} ∩ O → p.1 (G y) = u y) ∧
      (∀ y ∈ O, y k = 0 → u y = 0) := by
  obtain ⟨T, hTv, hTg, hT0⟩ := exists_chartH1Pullback hU hV hUb hVb hG hP hGU hPV hPG hGP
  let p' := T p
  have hp' : p' ∈ H1Zero {y | 0 < y k} := by
    have hpt := hT0 (V ∩ Ω) inter_subset_left p hp
    apply closure_mono (s := smoothH1Graph (U ∩ G ⁻¹' (V ∩ Ω)))
      (t := smoothH1Graph {y | 0 < y k}) _ hpt
    rintro a ⟨v, hv, hvs, hvsub, rfl⟩
    refine ⟨v, hv, hvs, ?_, rfl⟩
    intro y hy
    have hh := hvsub hy
    exact (hflat y hh.1).mp hh.2.2
  have hgrad : ∀ᵐ y ∂volume, y ∈ U → p'.2 y = chartGradientMap G y (p.2 (G y)) := by
    filter_upwards [hTg p] with y hy
    intro hyU
    simpa only [indicator_of_mem hyU] using hy
  obtain ⟨Ue, w, lam', hUe, hxUe, hUeU, hw, hlam', hwe, hBe⟩ :=
    exists_chart_local_ellipticity hU hG hP hGU hPG A hlam hell hx
  let U₀ := Ue ∩ G ⁻¹' W
  let V₀ := V ∩ P ⁻¹' U₀
  have hU₀ : IsOpen U₀ := hUe.inter (hW.preimage hG.continuous)
  have hV₀ : IsOpen V₀ := hV.inter (hU₀.preimage hP.continuous)
  have hU₀U : U₀ ⊆ U := inter_subset_left.trans hUeU
  have hx₀ : x ∈ U₀ := ⟨hxUe, hxW⟩
  have hG₀ : MapsTo G U₀ V₀ := by
    intro y hy
    exact ⟨hGU (hU₀U hy), by simpa only [mem_preimage, hPG y (hU₀U hy)] using hy⟩
  have hP₀ : MapsTo P V₀ U₀ := fun _ hz => hz.2
  have hV₀W : V₀ ⊆ W := by
    intro z hz
    have hh : G (P z) ∈ W := hz.2.2
    simpa only [hGP z hz.1] using hh
  have he₀ : WeakDivergenceEquation (V₀ ∩ Ω) (fun z => A z (p.2 z)) g := by
    intro φ hφ hs hsub
    exact he φ hφ hs (hsub.trans (fun z hz => ⟨hV₀W hz.1, hz.2⟩))
  have htrans := chart_weakDivergenceEquation hU₀ hV₀ hΩ
    (hVb.subset inter_subset_left) hG hP hG₀ hP₀
    (fun y hy => hPG y (hU₀U hy)) (fun z hz => hGP z hz.1) A p p' g w
    (fun y hy => hwe y hy.1)
    (hgrad.mono (fun y hy hz => hy (hU₀U hz))) he₀
  have hdom : U₀ ∩ G ⁻¹' Ω = {y | 0 < y k} ∩ U₀ := by
    ext y
    exact ⟨fun hy => ⟨(hflat y (hU₀U hy.1)).mp hy.2, hy.1⟩,
      fun hy => ⟨hy.2, (hflat y (hU₀U hy.2)).mpr hy.1⟩⟩
  rw [hdom] at htrans
  obtain ⟨θ, U₁, hU₁, hxU₁, hU₁₀, hθ, hθs, _, _, hθone⟩ :=
    exists_cutoff_with_open_plateau hU₀ hx₀
  let g' := fun y => w y * g (G y)
  have hg' : ContDiff ℝ ∞ g' := hw.mul (hg.comp hG)
  have hfmem : MemLp (fun y => θ y * g' y) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)) :=
    (hθ.mul hg').continuous.memLp_of_hasCompactSupport hθs.mul_right
  let f' := hfmem.toLp (fun y => θ y * g' y)
  have hfg : ∀ᵐ y ∂volume, y ∈ {y | 0 < y k} ∩ U₁ → f' y = g' y := by
    filter_upwards [hfmem.coeFn_toLp] with y hy
    intro hyU
    rw [hy, hθone y hyU.2, one_mul]
  have he' : WeakDivergenceEquation ({y | 0 < y k} ∩ U₁)
      (fun y => chartCoefficient A G P w y (p'.2 y)) f' := by
    apply OAI.Analysis.PDE.Variational.weakEquation_congr_on htrans (inter_subset_inter_right _ hU₁₀)
    · exact Eventually.of_forall (fun _ _ => rfl)
    · exact hfg
  obtain ⟨O, u, hO, hxO, hO₁, hu, hval, _, _, hzero⟩ :=
    halfspace_weak_solution_classical_dirichlet k (chartCoefficient A G P w)
      (contDiff_chartCoefficient hA hG hP hw) hlam' q hq hU₁
      (fun y hy => hBe y (hU₁₀ hy).1) p' hp' f' g' hg' hfg he' hxU₁
  refine ⟨O, u, hO, hxO, hO₁.trans (hU₁₀.trans hU₀U), hu, ?_, hzero⟩
  filter_upwards [hTv p, hval] with y hy hv
  intro hyO
  have hyU := hU₀U (hU₁₀ (hO₁ hyO.2))
  have hpv : p'.1 y = p.1 (G y) := by simpa only [indicator_of_mem hyU] using hy
  exact hpv.symm.trans (hv hyO)

end OAI.Analysis.PDE.Weak

import OAI.Analysis.PDE.Dirichlet.ContinuousComparison

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Topology Matrix ComplexOrder

/-- The maximum-principle Hessian gap is valid for an arbitrary collection of
quaternionic slots, in particular the physical three-slot fibers. -/
theorem slots_hessian_gap {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {f g r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hr : ContDiff ℝ 2 r)
    {ε : ℝ} (hε : 0 < ε) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s}
    (hrpos : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x)).PosDef)
    (hmax : IsLocalMax (fun y ↦ (f y + (-1 : ℝ) • g y) + ε • r y) x) :
    (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e g x - OAI.Analysis.PDE.Dirichlet.quaternionHessian e f x)).PosDef := by
  let F : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ := fun y ↦ (f y + (-1 : ℝ) • g y) + ε • r y
  have hF : ContDiff ℝ 2 F := (hf.add (hg.const_smul (-1 : ℝ))).add (hr.const_smul ε)
  have hN := OAI.LinearAlgebra.Moore.complexify_hessianMap_posSemidef e (OAI.Analysis.PDE.Dirichlet.realHessian_neg_posSemidef_of_localMax hF hmax)
  have hn : OAI.Analysis.Calculus.Quaternion.hessianMap e (-OAI.Analysis.PDE.Dirichlet.realHessian F x) = -OAI.Analysis.PDE.Dirichlet.quaternionHessian e F x := by
    rw [← neg_one_smul ℝ (OAI.Analysis.PDE.Dirichlet.realHessian F x), OAI.Analysis.Calculus.Quaternion.hessianMap_smul]
    simp only [OAI.Analysis.PDE.Dirichlet.quaternionHessian, neg_one_smul]
  rw [hn] at hN
  have hHF : OAI.Analysis.PDE.Dirichlet.quaternionHessian e F x =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e f x + (-1 : ℝ) • OAI.Analysis.PDE.Dirichlet.quaternionHessian e g x +
        ε • OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x := by
    dsimp only [F]
    rw [OAI.Analysis.PDE.Dirichlet.quaternionHessian_add_smul e (hf.add (hg.const_smul (-1 : ℝ))) hr,
      OAI.Analysis.PDE.Dirichlet.quaternionHessian_add_smul e hf hg]
  have hgap : OAI.Analysis.PDE.Dirichlet.quaternionHessian e g x - OAI.Analysis.PDE.Dirichlet.quaternionHessian e f x =
      -OAI.Analysis.PDE.Dirichlet.quaternionHessian e F x + ε • OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x := by
    rw [hHF]
    module
  rw [hgap, OAI.LinearAlgebra.Moore.complexify_add, OAI.LinearAlgebra.Moore.complexify_real_smul]
  exact Matrix.PosDef.posSemidef_add hN (hrpos.smul hε)

theorem slots_hessian_gap_at {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {f g r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (hr : ContDiffAt ℝ 2 r x)
    {ε : ℝ} (hε : 0 < ε)
    (hrpos : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x)).PosDef)
    (hmax : IsLocalMax (fun y ↦ (f y + (-1 : ℝ) • g y) + ε • r y) x) :
    (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e g x - OAI.Analysis.PDE.Dirichlet.quaternionHessian e f x)).PosDef := by
  obtain ⟨f', hf', hfeq⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hf
  obtain ⟨g', hg', hgeq⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hg
  obtain ⟨r', hr', hreq⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hr
  have heq : (fun y ↦ (f' y + (-1 : ℝ) • g' y) + ε • r' y) =ᶠ[𝓝 x]
      (fun y ↦ (f y + (-1 : ℝ) • g y) + ε • r y) := by
    filter_upwards [hfeq, hgeq, hreq] with y hfy hgy hry
    rw [hfy, hgy, hry]
  have hm : IsLocalMax (fun y ↦ (f' y + (-1 : ℝ) • g' y) + ε • r' y) x := by
    have heqx := heq.self_of_nhds
    dsimp only at heqx
    filter_upwards [hmax, heq] with y hy heqy
    rw [heqy, heqx]
    exact hy
  have hR : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e r' x)).PosDef := by
    rwa [OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ e hreq]
  have hh := slots_hessian_gap e hf' hg' hr' hε hR hm
  simpa only [OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ e hgeq, OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ e hfeq] using hh

/-- Nonlinear comparison on a periodic physical domain with arbitrary slots.
Compactness is imposed on a representative set, never on the full periodic
lift, and boundary data are imposed only on the true lateral boundary. -/
theorem slots_dirichlet_comparison_representatives {n s : ℕ} (hn : 1 ≤ n)
    (e : Fin s → Quaternion ℝ) {f g r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    {K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (hK : IsCompact K) (hKD : K ⊆ {x | r x ≤ 0})
    (hf : ContDiffOn ℝ 2 f {x | r x < 0}) (hg : ContDiffOn ℝ 2 g {x | r x < 0})
    (hr : ContDiff ℝ 2 r)
    (hfc : ContinuousOn f {x | r x ≤ 0}) (hgc : ContinuousOn g {x | r x ≤ 0})
    (hrep : ∀ x, r x ≤ 0 → p x ∈ K)
    (hrp : ∀ x, r x ≤ 0 → r (p x) = r x)
    (hfp : ∀ x, r x ≤ 0 → f (p x) = f x)
    (hgp : ∀ x, r x ≤ 0 → g (p x) = g x)
    (hrpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x)).PosDef)
    (hfpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e f x)).PosDef)
    (hdet : ∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e g x) ≤ OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e f x))
    (hbd : ∀ x, r x = 0 → f x ≤ g x) : ∀ x, r x ≤ 0 → f x ≤ g x := by
  intro x hx
  have heps (ε : ℝ) (hε : 0 < ε) : f x - g x + ε * r x ≤ 0 := by
    let F : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ := fun y ↦ (f y + (-1 : ℝ) • g y) + ε • r y
    have hF : ContinuousOn F {x | r x ≤ 0} :=
      (hfc.add (hgc.const_smul (-1 : ℝ))).add (hr.continuous.continuousOn.const_smul ε)
    have hFp : ∀ z, r z ≤ 0 → F (p z) = F z := by
      intro z hz
      simp only [F, hfp z hz, hgp z hz, hrp z hz]
    obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨p x, hrep x hx⟩ (hF.mono hKD)
    by_cases hyz : r y = 0
    · have hxy : F (p x) ≤ F y := hmax (hrep x hx)
      rw [hFp x hx] at hxy
      have hby := hbd y hyz
      dsimp only [F, smul_eq_mul] at hxy
      rw [hyz] at hxy
      linarith
    · have hyneg : r y < 0 := lt_of_le_of_ne (hKD hy) hyz
      have hlocal := OAI.Analysis.PDE.Dirichlet.localMax_of_compact_representatives p hr.continuous hrep hFp hyneg hmax
      have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr.continuous continuous_const
      have hgap := slots_hessian_gap_at e
        (hf.contDiffAt (hΩ.mem_nhds hyneg)) (hg.contDiffAt (hΩ.mem_nhds hyneg))
        hr.contDiffAt hε (hrpos y hyneg) hlocal
      have hne : OAI.Analysis.PDE.Dirichlet.quaternionHessian e g y ≠ OAI.Analysis.PDE.Dirichlet.quaternionHessian e f y := by
        intro heq
        have hd := hgap.diag_pos (i := ((⟨0, by omega⟩ : Fin n), (0 : Fin 2)))
        have hrr := (Complex.pos_iff.mp hd).1
        simp [heq, OAI.LinearAlgebra.Moore.complexify, OAI.LinearAlgebra.Moore.quaternionMatrix] at hrr
      have hlt := OAI.LinearAlgebra.Moore.mooreDet_lt_of_posSemidef_difference
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e f y) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e g y)
        (hfpos y hyneg) hgap.posSemidef hne
      exact False.elim (not_lt_of_ge (hdet y hyneg) hlt)
  have ht : Tendsto (fun ε : ℝ ↦ f x - g x + ε * r x) (𝓝[>] 0) (𝓝 (f x - g x)) := by
    have hc : Continuous (fun ε : ℝ ↦ f x - g x + ε * r x) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hle : f x - g x ≤ 0 := le_of_tendsto ht
    (Filter.Eventually.mono self_mem_nhdsWithin (fun ε hε ↦ heps ε hε))
  exact sub_nonpos.mp hle

theorem slots_dirichlet_comparison_lattice {n s : ℕ} (hn : 1 ≤ n)
    (slots : Fin s → Quaternion ℝ)
    {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {f g r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hf : ContDiffOn ℝ 2 f {x | r x < 0}) (hg : ContDiffOn ℝ 2 g {x | r x < 0})
    (hr : ContDiff ℝ 2 r)
    (hfc : ContinuousOn f {x | r x ≤ 0}) (hgc : ContinuousOn g {x | r x ≤ 0})
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hrper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hfper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f)
    (hgper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b g)
    (hrpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots r x)).PosDef)
    (hfpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots f x)).PosDef)
    (hdet : ∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots g x) ≤
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots f x))
    (hbd : ∀ x, r x = 0 → f x ≤ g x) : ∀ x, r x ≤ 0 → f x ≤ g x := by
  exact slots_dirichlet_comparison_representatives hn slots (OAI.Analysis.PDE.Dirichlet.latticeRepresentative e b)
    (OAI.Analysis.PDE.Dirichlet.isCompact_latticeSublevelCell e b hC hr.continuous) Set.inter_subset_right hf hg hr hfc hgc
    (fun x hx => OAI.Analysis.PDE.Dirichlet.latticeRepresentative_mem_sublevelCell e b hrper hbounded hx)
    (fun x _ => hrper.representative x) (fun x _ => hfper.representative x)
    (fun x _ => hgper.representative x) hrpos hfpos hdet hbd

end OAI.Analysis.PDE.Concentration

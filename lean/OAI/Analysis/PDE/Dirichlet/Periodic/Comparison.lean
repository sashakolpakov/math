import OAI.Analysis.PDE.Dirichlet.Comparison
import OAI.Analysis.PDE.Dirichlet.Periodic.Maximum
import OAI.Analysis.PDE.Dirichlet.Periodic.Calculus

open Set Filter Module
open scoped Topology Matrix ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem quaternionHessian_gap_posDef_of_barrier {n : ℕ}
    {f g r : CoordinateSpace n 4 → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hr : ContDiff ℝ 2 r)
    {ε : ℝ} (hε : 0 < ε) {x : CoordinateSpace n 4}
    (hrpos : (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hmax : IsLocalMax (fun y ↦ (f y + (-1 : ℝ) • g y) + ε • r y) x) :
    (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x - quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)).PosDef := by
  let F : CoordinateSpace n 4 → ℝ := fun y ↦ (f y + (-1 : ℝ) • g y) + ε • r y
  have hF : ContDiff ℝ 2 F := (hf.add (hg.const_smul (-1 : ℝ))).add (hr.const_smul ε)
  have hN := OAI.LinearAlgebra.Moore.complexify_hessianMap_posSemidef OAI.Analysis.Calculus.Quaternion.fourSlots
    (realHessian_neg_posSemidef_of_localMax hF hmax)
  have hn : OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (-realHessian F x) = -quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots F x := by
    rw [← neg_one_smul ℝ (realHessian F x), OAI.Analysis.Calculus.Quaternion.hessianMap_smul]
    simp only [quaternionHessian, neg_one_smul]
  rw [hn] at hN
  have hHF : quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots F x =
      quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x + (-1 : ℝ) • quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x +
        ε • quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x := by
    dsimp only [F]
    rw [quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots (hf.add (hg.const_smul (-1 : ℝ))) hr,
      quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hf hg]
  have hgap : quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x - quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x =
      -quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots F x + ε • quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x := by
    rw [hHF]
    module
  rw [hgap, OAI.LinearAlgebra.Moore.complexify_add, OAI.LinearAlgebra.Moore.complexify_real_smul]
  exact Matrix.PosDef.posSemidef_add hN (hrpos.smul hε)

/-- Nonlinear comparison on a periodic domain. A compact representative set
replaces compactness of the full lifted sublevel set. Only `r = 0` receives
boundary data; periodic cell faces do not. -/
theorem quaternionic_dirichlet_comparison_representatives {n : ℕ} (hn : 1 ≤ n)
    {f g r : CoordinateSpace n 4 → ℝ} {K : Set (CoordinateSpace n 4)}
    (p : CoordinateSpace n 4 → CoordinateSpace n 4)
    (hK : IsCompact K) (hKD : K ⊆ {x | r x ≤ 0})
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hr : ContDiff ℝ 2 r)
    (hrep : ∀ x, r x ≤ 0 → p x ∈ K)
    (hrp : ∀ x, r x ≤ 0 → r (p x) = r x)
    (hfp : ∀ x, r x ≤ 0 → f (p x) = f x)
    (hgp : ∀ x, r x ≤ 0 → g (p x) = g x)
    (hrpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hfpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)).PosDef)
    (hdet : ∀ x, r x < 0 →
      OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x) ≤ OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x))
    (hbd : ∀ x, r x = 0 → f x ≤ g x) : ∀ x, r x ≤ 0 → f x ≤ g x := by
  intro x hx
  have heps (ε : ℝ) (hε : 0 < ε) : f x - g x + ε * r x ≤ 0 := by
    let F : CoordinateSpace n 4 → ℝ := fun y ↦ (f y + (-1 : ℝ) • g y) + ε • r y
    have hF : ContDiff ℝ 2 F := (hf.add (hg.const_smul (-1 : ℝ))).add (hr.const_smul ε)
    have hFp : ∀ z, r z ≤ 0 → F (p z) = F z := by
      intro z hz
      simp only [F, hfp z hz, hgp z hz, hrp z hz]
    obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨p x, hrep x hx⟩ hF.continuous.continuousOn
    by_cases hyz : r y = 0
    · have hxy : F (p x) ≤ F y := hmax (hrep x hx)
      rw [hFp x hx] at hxy
      have hby := hbd y hyz
      dsimp only [F, smul_eq_mul] at hxy
      rw [hyz] at hxy
      linarith
    · have hyneg : r y < 0 := lt_of_le_of_ne (hKD hy) hyz
      have hlocal := localMax_of_compact_representatives p hr.continuous hrep hFp hyneg hmax
      have hgap := quaternionHessian_gap_posDef_of_barrier hf hg hr hε (hrpos y hyneg) hlocal
      have hne : quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y ≠ quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f y := by
        intro heq
        have hd := hgap.diag_pos (i := ((⟨0, by omega⟩ : Fin n), (0 : Fin 2)))
        have hr := (Complex.pos_iff.mp hd).1
        simp [heq, OAI.LinearAlgebra.Moore.complexify, OAI.LinearAlgebra.Moore.quaternionMatrix] at hr
      have hlt := OAI.LinearAlgebra.Moore.mooreDet_lt_of_posSemidef_difference
        (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f y) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)
        (hfpos y hyneg) hgap.posSemidef hne
      exact False.elim (not_lt_of_ge (hdet y hyneg) hlt)
  have ht : Tendsto (fun ε : ℝ ↦ f x - g x + ε * r x)
      (𝓝[>] 0) (𝓝 (f x - g x)) := by
    have hc : Continuous (fun ε : ℝ ↦ f x - g x + ε * r x) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hle : f x - g x ≤ 0 :=
    le_of_tendsto ht (Filter.Eventually.mono self_mem_nhdsWithin (fun ε hε ↦ heps ε hε))
  exact sub_nonpos.mp hle

section Lattice
variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

theorem quaternionic_dirichlet_comparison_lattice {n : ℕ} (hn : 1 ≤ n)
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {f g r : CoordinateSpace n 4 → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hr : ContDiff ℝ 2 r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hrper : LatticePeriodic e b r) (hfper : LatticePeriodic e b f)
    (hgper : LatticePeriodic e b g)
    (hrpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hfpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)).PosDef)
    (hdet : ∀ x, r x < 0 →
      OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x) ≤ OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x))
    (hbd : ∀ x, r x = 0 → f x ≤ g x) : ∀ x, r x ≤ 0 → f x ≤ g x := by
  exact quaternionic_dirichlet_comparison_representatives hn (latticeRepresentative e b)
    (isCompact_latticeSublevelCell e b hC hr.continuous) inter_subset_right hf hg hr
    (fun x hx ↦ latticeRepresentative_mem_sublevelCell e b hrper hbounded hx)
    (fun x _ ↦ hrper.representative x) (fun x _ ↦ hfper.representative x)
    (fun x _ ↦ hgper.representative x) hrpos hfpos hdet hbd

theorem quaternionic_dirichlet_uniqueness_lattice {n : ℕ} (hn : 1 ≤ n)
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {f g r : CoordinateSpace n 4 → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hr : ContDiff ℝ 2 r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hrper : LatticePeriodic e b r) (hfper : LatticePeriodic e b f)
    (hgper : LatticePeriodic e b g)
    (hrpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hfpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)).PosDef)
    (hgpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x)).PosDef)
    (hdet : ∀ x, r x < 0 →
      OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x) = OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x))
    (hbd : ∀ x, r x = 0 → f x = g x) : ∀ x, r x ≤ 0 → f x = g x := by
  intro x hx
  apply le_antisymm
  · exact quaternionic_dirichlet_comparison_lattice hn e b hC hf hg hr hbounded
      hrper hfper hgper hrpos hfpos (fun z hz ↦ (hdet z hz).ge)
      (fun z hz ↦ (hbd z hz).le) x hx
  · exact quaternionic_dirichlet_comparison_lattice hn e b hC hg hf hr hbounded
      hrper hgper hfper hrpos hgpos (fun z hz ↦ (hdet z hz).le)
      (fun z hz ↦ (hbd z hz).ge) x hx

end Lattice
end OAI.Analysis.PDE.Dirichlet

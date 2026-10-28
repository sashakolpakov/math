import OAI.Analysis.PDE.Weak.Boundary.Weak.Mixed
import OAI.Analysis.PDE.Weak.Elliptic.TestSupport

/-! Recovery of the normal flux derivative from the weak divergence
equation and the tangential flux derivatives. -/

noncomputable section
open Set Filter _root_.MeasureTheory InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem memLp_cell_component {H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m}
    (hH : MemLp H 2 volume) (i : Fin (m + 1)) : MemLp (fun x => H x i) 2 volume := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).toContinuousLinearMap
  exact ((ContinuousLinearMap.proj i).comp e).comp_memLp' hH

theorem WeakDivergenceEquation.normal_flux_derivative
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m}
    {f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hweak : WeakDivergenceEquation Ω H f)
    (hH : MemLp H 2 volume) (hf : MemLp f 2 volume)
    (k : Fin (m + 1)) (g : Fin (m + 1) → OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (hg : ∀ i, MemLp (g i) 2 volume)
    (hpartial : ∀ i, i ≠ k → ∀ φ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, g i x * φ x) = -(∫ x, H x i * fderiv ℝ φ x (Pi.single i 1))) :
    MemLp (fun x => -f x - ∑ i ∈ Finset.univ.erase k, g i x) 2 volume ∧
      ∀ φ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, (-f x - ∑ i ∈ Finset.univ.erase k, g i x) * φ x) =
        -(∫ x, H x k * fderiv ℝ φ x (Pi.single k 1)) := by
  have hsum : MemLp (fun x => ∑ i ∈ Finset.univ.erase k, g i x) 2 volume :=
    memLp_finsetSum _ (fun i _ => hg i)
  refine ⟨hf.neg.sub hsum, ?_⟩
  intro φ hφ hs hφΩ
  have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hs
  have hD (i : Fin (m + 1)) : MemLp (fun x => fderiv ℝ φ x (Pi.single i 1)) 2 volume := by
    exact (OAI.Analysis.PDE.Green.continuous_directional (hφ.of_le (by simp)) _).memLp_of_hasCompactSupport
      (hs.fderiv_apply ℝ _)
  have hi (i : Fin (m + 1)) : Integrable (fun x => H x i * fderiv ℝ φ x (Pi.single i 1)) :=
    (memLp_cell_component hH i).integrable_mul (hD i)
  have hgφ (i : Fin (m + 1)) : Integrable (fun x => g i x * φ x) :=
    (hg i).integrable_mul hφ2
  have hfφ : Integrable (fun x => f x * φ x) := hf.integrable_mul hφ2
  have he := hweak φ hφ hs hφΩ
  have hinner (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
      inner ℝ (H x) (OAI.Analysis.PDE.Variational.cellGradient φ x) = ∑ i, H x i * fderiv ℝ φ x (Pi.single i 1) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, OAI.Analysis.PDE.Variational.cellGradient_apply]
    congr 1
    funext i
    ring
  simp_rw [hinner] at he
  rw [integral_finsetSum _ (fun i _ => hi i)] at he
  have herase : (∑ i ∈ Finset.univ.erase k, ∫ x, H x i * fderiv ℝ φ x (Pi.single i 1)) =
      -(∑ i ∈ Finset.univ.erase k, ∫ x, g i x * φ x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hp := hpartial i (Finset.mem_erase.mp hi).1 φ hφ hs hφΩ
    linarith
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun i => ∫ x, H x i * fderiv ℝ φ x (Pi.single i 1)) (Finset.mem_univ k)
  rw [herase, he] at hsplit
  have hprod (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
      (-f x - ∑ i ∈ Finset.univ.erase k, g i x) * φ x =
        -(f x * φ x) - ∑ i ∈ Finset.univ.erase k, g i x * φ x := by
    rw [sub_mul, neg_mul, Finset.sum_mul]
  simp_rw [hprod]
  have hsφ : Integrable (fun x => ∑ i ∈ Finset.univ.erase k, g i x * φ x) :=
    integrable_finsetSum _ (fun i _ => hgφ i)
  have hI : (∫ x, -(f x * φ x) - ∑ i ∈ Finset.univ.erase k, g i x * φ x) =
      (∫ x, -(f x * φ x)) - ∫ x, ∑ i ∈ Finset.univ.erase k, g i x * φ x :=
    integral_sub (μ := volume) (f := fun x => -(f x * φ x))
      (g := fun x => ∑ i ∈ Finset.univ.erase k, g i x * φ x) hfφ.neg hsφ
  rw [hI, integral_neg, integral_finsetSum _ (fun i _ => hgφ i)]
  linarith

end OAI.Analysis.PDE.Weak

import OAI.RepresentationTheory.Weil.AdelicSplitting.CompactCharacter
import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanNormalization

/-! # Self Dual Lattice -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.SelfDualLattice.LocalAnalysis

noncomputable section

/-! A compact open lattice equal to its character annihilator has measure
one and its indicator is fixed by the exactly normalized Fourier operator. -/

open _root_.MeasureTheory
open scoped Classical

section Annihilator
variable {k : Type} [NormedField k] {n : ℕ}

def ringLatticeSubgroup (R : Subring k) : AddSubgroup (Local.FunctionsMetaplectic.Construction.Position k n) where
  carrier := Set.univ.pi (fun _ : Fin n => (R : Set k))
  zero_mem' := by intro i _; exact R.zero_mem
  add_mem' hx hy i hi := R.add_mem (hx i hi) (hy i hi)
  neg_mem' hx i hi := R.neg_mem (hx i hi)

theorem ringLattice_annihilator_eq (R : Subring k) (ψ : AddChar k ℂ)
    (hψ : ∀ t ∈ R, ψ t = 1)
    (hAnn : ∀ u : k, (∀ t ∈ R, ψ (u * t) = 1) → u ∈ R) :
    CompactCharacter.LocalAnalysis.additiveAnnihilator ψ (ringLatticeSubgroup (n := n) R) = ringLatticeSubgroup R := by
  ext x
  constructor
  · intro hx i _
    apply hAnn
    intro t ht
    have hsingle : (Pi.single i t : Local.FunctionsMetaplectic.Construction.Position k n) ∈ ringLatticeSubgroup R := by
      intro j _
      by_cases hj : j = i
      · subst j; simpa using ht
      · simp [Pi.single_eq_of_ne hj]
    have h := hx (Pi.single i t) hsingle
    simpa [Local.FunctionsMetaplectic.Construction.dot, Pi.single_apply] using h
  · intro hx y hy
    apply hψ
    apply R.sum_mem
    intro i _
    exact R.mul_mem (hx i (Set.mem_univ i)) (hy i (Set.mem_univ i))

end Annihilator

variable {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
  [SecondCountableTopology k] {n : ℕ}

theorem selfDual_lattice_fourier_fixed
    (ψ : AddChar k ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (U : OpenAddSubgroup (Local.FunctionsMetaplectic.Construction.Position k n)) (hU : IsCompact (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)))
    (hAnn : CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U.toAddSubgroup = U.toAddSubgroup)
    (hInv : ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) x,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val) x = f.val (-x)) :
    μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)) = 1 ∧
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ ((U : Set (Local.FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ))) =
        (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ)) := by
  let f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n :=
    ⟨(U : Set (Local.FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ)),
      Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem (CompactCharacter.LocalAnalysis.subgroup_indicator_locallyConstant U)
        (CompactCharacter.LocalAnalysis.subgroup_indicator_compactSupport U hU)⟩
  let c : ℝ := μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k n))
  have hF : Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val = (c : ℂ) • f.val := by
    funext x
    rw [show f.val = (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ)) from rfl,
      CompactCharacter.LocalAnalysis.fourier_indicator_subgroup, hAnn]
    by_cases hx : x ∈ U <;> simp [hx, c]
  have hf0 : f.val 0 = 1 := by simp [f]
  have he := hInv f 0
  rw [hF, Local.FunctionsMetaplectic.Construction.fourierIntegral_smul] at he
  change (c : ℂ) * Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val 0 = f.val (-0) at he
  rw [hF] at he
  simp only [Pi.smul_apply, smul_eq_mul, neg_zero, hf0, mul_one] at he
  have hsq : c ^ 2 = (1 : ℝ) ^ 2 := by
    have h : (c : ℂ) ^ 2 = 1 := by simpa only [sq] using he
    rw [one_pow]
    exact_mod_cast h
  have hc : c = 1 := (sq_eq_sq₀ (measureReal_nonneg) (by norm_num)).mp hsq
  refine ⟨hc, ?_⟩
  change Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val = f.val
  rw [hF, hc]
  simp

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.SelfDualLattice.LocalAnalysis

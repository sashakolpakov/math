import OAI.AlgebraicGeometry.Comparison.Betti.MixedJetPartialDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-! # Mixed Jet Differential -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.MixedJetDifferential.Dolbeault

noncomputable section

/-! The actual joint derivative of a mixed jet is the sum of two
continuous linear images of its adjacent parameter and line jets. -/

open Set Filter
open scoped ContDiff _root_.Topology

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

def mixedJetParameterDifferential (k : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => P) F →L[ℝ]
      (P × ℂ →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F) where
  toFun T := T.curryLeft.comp (ContinuousLinearMap.fst ℝ P ℂ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => P) F).continuous.clm_comp continuous_const

def mixedJetLineDifferential (k : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F →L[ℝ]
      (P × ℂ →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F) where
  toFun T := ((ContinuousLinearMap.lsmul ℝ ℂ).flip T).comp (ContinuousLinearMap.snd ℝ P ℂ)
  map_add' A B := by
    rw [map_add]
    rfl
  map_smul' a T := by
    rw [map_smul]
    rfl
  cont := (ContinuousLinearMap.lsmul ℝ ℂ).flip.continuous.clm_comp continuous_const

theorem mixedJetDifferential_contDiffOn {n : ℕ∞ω} {S : Set (P × ℂ)} (k : ℕ)
    {A : P × ℂ → ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => P) F}
    {B : P × ℂ → ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F}
    (hA : ContDiffOn ℝ n A S) (hB : ContDiffOn ℝ n B S) :
    ContDiffOn ℝ n (fun q => mixedJetParameterDifferential (P := P) (F := F) k (A q) +
      mixedJetLineDifferential (P := P) (F := F) k (B q)) S := by
  have hp := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
      (E := ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => P) F)
      (F := P × ℂ →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F)
      (mixedJetParameterDifferential (P := P) (F := F) k)
  have hl := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
      (E := ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F)
      (F := P × ℂ →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F)
      (mixedJetLineDifferential (P := P) (F := F) k)
  have h1 : ContDiffOn ℝ n (fun q => mixedJetParameterDifferential (P := P) (F := F) k (A q)) S := by
    convert hp.comp_contDiffOn hA using 1
    rfl
  have h2 : ContDiffOn ℝ n (fun q => mixedJetLineDifferential (P := P) (F := F) k (B q)) S := by
    convert hl.comp_contDiffOn hB using 1
    rfl
  exact h1.add h2

variable [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P] [CompleteSpace F]

theorem hasFDerivAt_mixedParameterJet {g : P × ℂ → F} (hg : ContDiff ℝ ∞ g)
    {U : Set ℂ} (hU : IsOpen U) (hhol : ∀ p : P, DifferentiableOn ℂ (fun z => g (p, z)) U)
    (k l : ℕ) {q : P × ℂ} (hq : q.2 ∈ U) :
    HasFDerivAt (MixedJetAlgebra.Dolbeault.mixedParameterJet g k l)
      (mixedJetParameterDifferential (P := P) (F := F) k (MixedJetAlgebra.Dolbeault.mixedParameterJet g (k + 1) l q) +
        mixedJetLineDifferential (P := P) (F := F) k (MixedJetAlgebra.Dolbeault.mixedParameterJet g k (l + 1) q)) q := by
  have hparam : ∀ᶠ y in 𝓝 q, HasFDerivAt (fun p => MixedJetAlgebra.Dolbeault.mixedParameterJet g k l (p, y.2))
      (MixedJetAlgebra.Dolbeault.mixedParameterJet g (k + 1) l y).curryLeft y.1 := by
    filter_upwards [(isOpen_univ.prod hU).mem_nhds (show q ∈ univ ×ˢ U from ⟨mem_univ _, hq⟩)] with y hy
    exact MixedJetPartialDerivatives.Dolbeault.hasFDerivAt_mixedParameterJet_parameter hg hU hhol k l y.1 hy.2
  have hline : ∀ᶠ y in 𝓝 q, HasFDerivAt (fun z => MixedJetAlgebra.Dolbeault.mixedParameterJet g k l (y.1, z))
      ((ContinuousLinearMap.lsmul ℝ ℂ).flip (MixedJetAlgebra.Dolbeault.mixedParameterJet g k (l + 1) y)) y.2 := by
    filter_upwards [(isOpen_univ.prod hU).mem_nhds (show q ∈ univ ×ˢ U from ⟨mem_univ _, hq⟩)] with y hy
    convert (MixedJetPartialDerivatives.Dolbeault.hasDerivAt_mixedParameterJet_line hg hU hhol k l y.1 hy.2).hasFDerivAt.restrictScalars ℝ using 1; rfl
  have hc1 : ContinuousAt (fun y => (MixedJetAlgebra.Dolbeault.mixedParameterJet g (k + 1) l y).curryLeft) q :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => P) F).continuous.continuousAt.comp
      ((MixedJetAlgebra.Dolbeault.mixedParameterJet_smooth hg hU hhol (k + 1) l).contDiffAt
        ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _, hq⟩)).continuousAt
  have hc2 : ContinuousAt (fun y => (ContinuousLinearMap.lsmul ℝ ℂ).flip
      (MixedJetAlgebra.Dolbeault.mixedParameterJet g k (l + 1) y)) q :=
    (ContinuousLinearMap.lsmul ℝ ℂ).flip.continuous.continuousAt.comp
      ((MixedJetAlgebra.Dolbeault.mixedParameterJet_smooth hg hU hhol k (l + 1)).contDiffAt
        ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _, hq⟩)).continuousAt
  have h := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ)
    (f := fun p z => MixedJetAlgebra.Dolbeault.mixedParameterJet g k l (p, z))
    (f₁ := fun p z => (MixedJetAlgebra.Dolbeault.mixedParameterJet g (k + 1) l (p, z)).curryLeft)
    (f₂ := fun p z => (ContinuousLinearMap.lsmul ℝ ℂ).flip (MixedJetAlgebra.Dolbeault.mixedParameterJet g k (l + 1) (p, z)))
    hparam hline hc1 hc2
  convert h.hasFDerivAt using 1 <;> rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.MixedJetDifferential.Dolbeault

import OAI.Geometry.Nikodym.MajorantLp
import OAI.Geometry.Nikodym.VolumeNormalization

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Filter
open scoped ENNReal
namespace OAI.Geometry.Nikodym


theorem nikodym_measurable_lp_bound (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : Space (d+1) → ℂ, Measurable f → MemLp f (d+1 : ℕ) volume →
      eLpNorm (nikodymMaximal δ f) (d+1 : ℕ) volume ≤
        ENNReal.ofReal (C*δ^(-ε))*eLpNorm f (d+1 : ℕ) volume := by
  obtain ⟨C,hC,hbound⟩ := tubeMajorant_lp_bound hK hd hε
  obtain ⟨c,hc,hmajor⟩ := exists_nikodymMajorant_bound (d:=d)
  refine ⟨c*C,mul_pos hc hC,?_⟩
  intro δ hδ hδ1 f hf hfp
  obtain ⟨N,hN⟩ := hmajor δ hδ hδ1
  have h : eLpNorm (nikodymMaximal δ f) (d+1 : ℕ) volume ≤
      ENNReal.ofReal c * eLpNorm (tubeMajorant δ N f) (d+1 : ℕ) volume := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' (d+1 : ℕ)
      (measurable_nikodymMaximal δ f hf.aestronglyMeasurable).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by simpa using hN f hf x)
  apply h.trans ((mul_le_mul' le_rfl (hbound N δ hδ hδ1 f hf hfp)).trans_eq _)
  rw [ENNReal.ofReal_mul (mul_nonneg hc.le hC.le),ENNReal.ofReal_mul hc.le,
    ENNReal.ofReal_mul hC.le]
  ac_rfl

theorem nikodymMaximal_congr_ae {n : ℕ} {f g : Space n → ℂ}
    (h : f =ᵐ[volume] g) (δ : ℝ) : nikodymMaximal δ f = nikodymMaximal δ g := by
  funext x
  unfold nikodymMaximal
  apply congrArg iSup
  funext ω
  apply congrArg iSup
  funext hω
  apply congrArg iSup
  funext t
  apply congrArg iSup
  funext ht
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae h] with y hy
  rw [hy]

theorem nikodym_lp_bound (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : Space (d+1) → ℂ, MemLp f (d+1 : ℕ) volume →
      MemLp (nikodymMaximal δ f) (d+1 : ℕ) volume ∧
      eLpNorm (nikodymMaximal δ f) (d+1 : ℕ) volume ≤
        ENNReal.ofReal (C*δ^(-ε))*eLpNorm f (d+1 : ℕ) volume := by
  obtain ⟨C,hC,hbound⟩ := nikodym_measurable_lp_bound hK hd hε
  refine ⟨C,hC,?_⟩
  intro δ hδ hδ1 f hf
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hgn : eLpNorm g (d+1 : ℕ) volume = eLpNorm f (d+1 : ℕ) volume :=
    eLpNorm_congr_ae hfg.symm
  have hgp : MemLp g (d+1 : ℕ) volume := by
    change eLpNorm _ _ _ < ⊤
    rw [hgn]
    exact hf
  have h := hbound δ hδ hδ1 g hg hgp
  rw [← nikodymMaximal_congr_ae hfg δ,hgn] at h
  refine ⟨h.trans_lt ?_,h⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf

end OAI.Geometry.Nikodym
namespace OAI.Geometry.Nikodym

theorem kakeyaMaximal_implies_nikodymMaximal (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture) :
    NikodymMaximalConjecture := by
  intro n hn ε hε
  cases n with
  | zero => omega
  | succ d => exact OAI.Geometry.Nikodym.nikodym_lp_bound hK (by omega) hε

end OAI.Geometry.Nikodym

import OAI.MeasureTheory.Kakeya.Geometry

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set
open scoped ENNReal
namespace OAI.Geometry.Nikodym

/-- The Nikodym maximal function from `further_geometry.tex`: the supremum
over all unit segments containing the evaluation point. The parameter `t`
records the position of that point on the centered segment. -/
def nikodymMaximal {n : ℕ} (δ : ℝ) (f : Space n → ℂ) (x : Space n) : ℝ≥0∞ :=
  ⨆ (ω : Space n) (_ : ‖ω‖ = 1) (t : ℝ) (_ : t ∈ Icc (-(1/2 : ℝ)) (1/2)),
    (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω (x-t • ω), ‖f y‖ₑ) / volume (OAI.MeasureTheory.Kakeya.tube δ ω (x-t • ω))

def NikodymMaximalConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : Space n → ℂ, MemLp f n volume →
        MemLp (nikodymMaximal δ f) n volume ∧
        eLpNorm (nikodymMaximal δ f) n volume ≤
          ENNReal.ofReal (C*δ^(-ε)) * eLpNorm f n volume

theorem tube_average_le_nikodymMaximal {n : ℕ} {δ : ℝ} (f : Space n → ℂ)
    {ω a x : Space n} (hω : ‖ω‖ = 1) (hx : x ∈ OAI.MeasureTheory.Kakeya.unitSegment ω a) :
    (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω a, ‖f y‖ₑ) / volume (OAI.MeasureTheory.Kakeya.tube δ ω a) ≤ nikodymMaximal δ f x := by
  rcases hx with ⟨t,ht,rfl⟩
  unfold nikodymMaximal
  apply le_iSup_of_le ω
  apply le_iSup_of_le hω
  apply le_iSup_of_le t
  apply le_iSup_of_le ht
  simp only [add_sub_cancel_right,le_refl]

theorem nikodymMaximal_mono {n : ℕ} {δ : ℝ} {f g : Space n → ℂ}
    (h : ∀ y, ‖f y‖ₑ ≤ ‖g y‖ₑ) (x : Space n) :
    nikodymMaximal δ f x ≤ nikodymMaximal δ g x := by
  unfold nikodymMaximal
  apply iSup_mono
  intro ω
  apply iSup_mono
  intro hω
  apply iSup_mono
  intro t
  apply iSup_mono
  intro ht
  exact ENNReal.div_le_div_right (lintegral_mono h) _

end OAI.Geometry.Nikodym

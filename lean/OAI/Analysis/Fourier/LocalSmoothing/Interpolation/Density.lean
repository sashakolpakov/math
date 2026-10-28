import OAI.Analysis.Fourier.SquareFunction.ConvolutionDensity

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation

/-- A finite (not necessarily uniform) rough operator bound permits the
sharp Schwartz bound to pass to integrable Lp inputs. -/
theorem bound_of_schwartz_dense {n : ℕ} {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (T : (Space n → ℂ) → Y → ℂ)
    (hadd : ∀ g h, Integrable g → Integrable h → ∀ y,
      T (fun x => g x + h x) y = T g y + T h y)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {A B : ℝ≥0∞}
    (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hsharp : ∀ g : SchwartzMap (Space n) ℂ,
      eLpNorm (T g) p ν ≤ A * eLpNorm g p volume)
    (hrough : ∀ g, Measurable g → Integrable g → MemLp g p volume →
      eLpNorm (T g) p ν ≤ B * eLpNorm g p volume)
    {f : Space n → ℂ} (hfm : Measurable f) (hfi : Integrable f) (hfp : MemLp f p volume) :
    eLpNorm (T f) p ν ≤ A * eLpNorm f p volume := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨η,hη,herror⟩ := OAI.Analysis.Fourier.SquareFunction.exists_pos_mul_ofReal_le
    (C := A + B) (ENNReal.add_ne_top.mpr ⟨hA,hB⟩) hε
  obtain ⟨g,hg⟩ := OAI.Analysis.Fourier.SquareFunction.exists_schwartz_eLpNorm_sub_le hp hpt hfp hη
  have hnormg : eLpNorm g p volume ≤ eLpNorm f p volume + ENNReal.ofReal η := by
    have hid : (g : Space n → ℂ) = f - (f - (g : Space n → ℂ)) := by ext x; simp
    rw [hid]
    exact (eLpNorm_sub_le hp).trans (add_le_add le_rfl hg)
  have hid : (fun x => g x + (f - (g : Space n → ℂ)) x) = f := by ext x; simp
  have hsum : T f = fun y => T g y + T (f - (g : Space n → ℂ)) y := by
    funext y
    simpa only [hid] using hadd g (f - (g : Space n → ℂ)) g.integrable (hfi.sub g.integrable) y
  rw [hsum]
  calc
    _ ≤ eLpNorm (T g) p ν + eLpNorm (T (f - (g : Space n → ℂ))) p ν := eLpNorm_add_le hp
    _ ≤ A * eLpNorm g p volume + B * eLpNorm (f - (g : Space n → ℂ)) p volume :=
      add_le_add (hsharp g) (hrough _ (hfm.sub g.continuous.measurable)
        (hfi.sub g.integrable) (hfp.sub (g.memLp p volume)))
    _ ≤ A * (eLpNorm f p volume + ENNReal.ofReal η) + B * ENNReal.ofReal η := by gcongr
    _ = A * eLpNorm f p volume + (A + B) * ENNReal.ofReal η := by ring
    _ ≤ _ := add_le_add le_rfl herror

end OAI.Analysis.Fourier.LocalSmoothing.Interpolation

import OAI.Geometry.Nikodym.ProjectiveIntegral
import OAI.Geometry.Nikodym.ProjectiveKakeya

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Module
open scoped ENNReal
namespace OAI.Geometry.Nikodym


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def projectivePullback {n : ℕ} (L : (E × ℝ) ≃L[ℝ] Space n)
    (f : Space n → ℂ) (y : Space n) : ℂ := f (L (projective (L.symm y)))

theorem measurable_projectivePullback {n : ℕ} (L : (E × ℝ) ≃L[ℝ] Space n)
    {f : Space n → ℂ} (hf : Measurable f) : Measurable (projectivePullback L f) :=
  hf.comp (L.continuous.measurable.comp (measurable_projective.comp L.symm.continuous.measurable))

theorem tube_mass_le_kakeya {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (f : Space n → ℂ) (ω c : Space n) :
    (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω c, ‖f y‖ₑ) ≤ volume (OAI.MeasureTheory.Kakeya.tube δ ω c) * OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f ω := by
  have h := le_iSup (fun c : Space n =>
    (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω c, ‖f y‖ₑ) / volume (OAI.MeasureTheory.Kakeya.tube δ ω c)) c
  have hv0 := (OAI.MeasureTheory.Kakeya.volume_tube_pos hδ ω c).ne'
  have hvtop := (OAI.MeasureTheory.Kakeya.volume_tube_lt_top δ ω c).ne
  have hh := (ENNReal.div_le_iff hv0 hvtop).mp h
  simpa only [OAI.MeasureTheory.Kakeya.kakeyaMaximal,mul_comm] using hh

/-- The concrete normalized strip is controlled by the actual Kakeya
maximal operator after the projective involution. -/
theorem normalized_strip_mass_le_kakeya {n : ℕ}
    (L : (E × ℝ) ≃L[ℝ] Space n) (x v : E) {A X V δ : ℝ}
    (hA : 0 < A) (hL : ‖(L : (E × ℝ) →L[ℝ] Space n)‖ ≤ A)
    (hX : 0 ≤ X) (hV : 0 ≤ V) (hx : ‖x‖ ≤ X) (hv : ‖v‖ ≤ V)
    (hwn : ‖L (x,1)‖ ≤ 2) (hδ : 0 < δ) (hδhalf : δ ≤ 1/2)
    {f : Space n → ℂ} (hf : Measurable f) :
    let η := A*((2+4*(X+2*V+1))*δ)
    let ω := ‖L (x,1)‖⁻¹ • L (x,1)
    let c := L (v,0)+(3/4 : ℝ) • L (x,1)
    (∫⁻ p in neighborhood δ (linePiece x v 1 2), ‖f (L p)‖ₑ
        ∂Measure.map L.symm volume) ≤
      ENNReal.ofReal (projectiveDistortion (3:ℝ)⁻¹ ((X+2*V+1)/(1/2))) ^
        finrank ℝ (E × ℝ) * volume (OAI.MeasureTheory.Kakeya.tube η ω c) *
          OAI.MeasureTheory.Kakeya.kakeyaMaximal η (projectivePullback L f) ω := by
  dsimp only
  let μ : Measure (E × ℝ) := Measure.map L.symm volume
  let : μ.IsAddHaarMeasure := L.symm.isAddHaarMeasure_map volume
  let η := A*((2+4*(X+2*V+1))*δ)
  let ω := ‖L (x,1)‖⁻¹ • L (x,1)
  let c := L (v,0)+(3/4 : ℝ) • L (x,1)
  let T := OAI.MeasureTheory.Kakeya.tube η ω c
  have hη : 0 < η := by dsimp [η]; positivity
  have hw : L (x,1) ≠ 0 := by
    intro he
    have hh : (x,(1:ℝ)) = 0 := L.injective (he.trans (map_zero L).symm)
    have := congrArg Prod.snd hh
    norm_num at this
  have hT : MeasurableSet T := OAI.MeasureTheory.Kakeya.measurableSet_tube _ _ _
  have hmap : MapsTo projective (neighborhood δ (linePiece x v 1 2)) (L ⁻¹' T) := by
    intro p hp
    exact linear_projective_neighborhood_subset_tube (L : (E × ℝ) →L[ℝ] Space n)
      x v hA hL hX hV hx hv hw hwn hδ hδhalf ⟨projective p,⟨p,hp,rfl⟩,rfl⟩
  have htrans := lintegral_projective_strip μ (a:=1/2) (b:=3) (R:=X+2*V+1)
    (by norm_num) (by norm_num) (by positivity)
    (isOpen_neighborhood _ _).measurableSet (hT.preimage L.continuous.measurable)
    (normalized_neighborhood_in_strip hx hv hδhalf) hmap
    ((hf.comp L.continuous.measurable).enorm)
  have hchange : (∫⁻ q in L ⁻¹' T, ‖f (L (projective q))‖ₑ ∂μ) =
      ∫⁻ y in T, ‖projectivePullback L f y‖ₑ := by
    have hF : Measurable (fun q : E × ℝ => ‖f (L (projective q))‖ₑ) := by
      exact (hf.comp (L.continuous.measurable.comp measurable_projective)).enorm
    have hpre : L.symm ⁻¹' (L ⁻¹' T) = T := by ext y; simp
    rw [show μ = Measure.map L.symm volume from rfl,
      setLIntegral_map (hT.preimage L.continuous.measurable) hF
        L.symm.continuous.measurable,hpre]
    rfl
  simp only [Function.comp_apply] at htrans
  rw [hchange] at htrans
  exact htrans.trans (by
    rw [mul_assoc]
    exact mul_le_mul' le_rfl (tube_mass_le_kakeya hη (projectivePullback L f) ω c))

end OAI.Geometry.Nikodym

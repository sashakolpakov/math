import OAI.Geometry.Nikodym.ChristoffelDerivative
import OAI.Geometry.Nikodym.ParallelMetric

noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

open Set
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (g : SmoothCoordinateMetric E)

def oscillatorFirst (_ : SmoothCoordinateMetric E) (κ : ℝ) (J A : ℝ → E) (t : ℝ) : E :=
  curvatureCos κ t • J t - curvatureSin κ t • A t

def oscillatorSecond (_ : SmoothCoordinateMetric E) (κ : ℝ) (J A : ℝ → E) (t : ℝ) : E :=
  (κ * curvatureSin κ t) • J t + curvatureCos κ t • A t

omit [FiniteDimensional ℝ E] in
theorem oscillator_reconstruction (κ : ℝ) (J A : ℝ → E) (t : ℝ) :
    J t = curvatureCos κ t • g.oscillatorFirst κ J A t +
      curvatureSin κ t • g.oscillatorSecond κ J A t := by
  calc
    J t = ((curvatureCos κ t)^2 + κ*(curvatureSin κ t)^2) • J t := by
      rw [curvature_energy,one_smul]
    _ = _ := by dsimp [SmoothCoordinateMetric.oscillatorFirst,SmoothCoordinateMetric.oscillatorSecond]; module

theorem hasDerivAt_oscillatorFirst {κ t : ℝ} {γ v J A : ℝ → E}
    (hJ : HasDerivAt J (A t - g.christoffel (γ t) (v t) (J t)) t)
    (hA : HasDerivAt A ((-κ) • J t - g.christoffel (γ t) (v t) (A t)) t) :
    HasDerivAt (g.oscillatorFirst κ J A)
      (-g.christoffel (γ t) (v t) (g.oscillatorFirst κ J A t)) t := by
  have hd := ((hasDerivAt_curvatureCos κ t).smul hJ).sub
    ((hasDerivAt_curvatureSin κ t).smul hA)
  convert hd using 1
  · rfl
  · change -(g.christoffelBilinear (γ t) (v t)
      (curvatureCos κ t • J t - curvatureSin κ t • A t)) = _
    simp only [map_sub,map_smul,SmoothCoordinateMetric.christoffelBilinear_apply]
    module

theorem hasDerivAt_oscillatorSecond {κ t : ℝ} {γ v J A : ℝ → E}
    (hJ : HasDerivAt J (A t - g.christoffel (γ t) (v t) (J t)) t)
    (hA : HasDerivAt A ((-κ) • J t - g.christoffel (γ t) (v t) (A t)) t) :
    HasDerivAt (g.oscillatorSecond κ J A)
      (-g.christoffel (γ t) (v t) (g.oscillatorSecond κ J A t)) t := by
  have hd := (((hasDerivAt_curvatureSin κ t).const_mul κ).smul hJ).add
    ((hasDerivAt_curvatureCos κ t).smul hA)
  convert hd using 1
  · rfl
  · change -(g.christoffelBilinear (γ t) (v t)
      ((κ*curvatureSin κ t) • J t + curvatureCos κ t • A t)) = _
    simp only [map_add,map_smul,SmoothCoordinateMetric.christoffelBilinear_apply]
    module

/-- Parallel fields initially zero remain zero, obtained directly from
metric compatibility and positivity rather than an assumed transport. -/
theorem parallel_eq_zero {I : Set ℝ} (hI : Convex ℝ I) (h0 : 0 ∈ I)
    {γ v W : ℝ → E} (hdom : ∀ t ∈ I, γ t ∈ g.domain)
    (hγ : ∀ t ∈ I, HasDerivAt γ (v t) t)
    (hW : ∀ t ∈ I, HasDerivAt W (-g.christoffel (γ t) (v t) (W t)) t)
    (hW0 : W 0 = 0) {t : ℝ} (ht : t ∈ I) : W t = 0 := by
  by_contra hn
  have he := g.parallel_inner_eq hI hdom hγ hW hW h0 ht
  have hp := g.positive (γ t) (hdom t ht) (W t) hn
  simp only [hW0,SmoothCoordinateMetric.inner,map_zero,inner_zero_left] at he
  exact hp.ne' he

theorem oscillator_first_zero {I : Set ℝ} (hI : Convex ℝ I) (h0 : 0 ∈ I)
    (κ : ℝ) {γ v J A : ℝ → E} (hdom : ∀ t ∈ I, γ t ∈ g.domain)
    (hγ : ∀ t ∈ I, HasDerivAt γ (v t) t)
    (hJ : ∀ t ∈ I, HasDerivAt J (A t - g.christoffel (γ t) (v t) (J t)) t)
    (hA : ∀ t ∈ I, HasDerivAt A ((-κ) • J t - g.christoffel (γ t) (v t) (A t)) t)
    (hJ0 : J 0 = 0) {t : ℝ} (ht : t ∈ I) :
    g.oscillatorFirst κ J A t = 0 := by
  apply g.parallel_eq_zero hI h0 hdom hγ
    (fun s hs => g.hasDerivAt_oscillatorFirst (hJ s hs) (hA s hs)) _ ht
  simp only [SmoothCoordinateMetric.oscillatorFirst,curvatureCos_zero,curvatureSin_zero,hJ0,
    smul_zero,zero_smul,sub_zero]

/-- The transverse Jacobi metric is the exact sine-square model, deduced
from genuine covariant ODEs and the actual metric. -/
theorem covariant_oscillator_inner {I : Set ℝ} (hI : Convex ℝ I) (h0 : 0 ∈ I)
    (κ : ℝ) {γ v J₁ A₁ J₂ A₂ : ℝ → E} (hdom : ∀ t ∈ I, γ t ∈ g.domain)
    (hγ : ∀ t ∈ I, HasDerivAt γ (v t) t)
    (hJ₁ : ∀ t ∈ I, HasDerivAt J₁ (A₁ t - g.christoffel (γ t) (v t) (J₁ t)) t)
    (hA₁ : ∀ t ∈ I, HasDerivAt A₁ ((-κ) • J₁ t - g.christoffel (γ t) (v t) (A₁ t)) t)
    (hJ₂ : ∀ t ∈ I, HasDerivAt J₂ (A₂ t - g.christoffel (γ t) (v t) (J₂ t)) t)
    (hA₂ : ∀ t ∈ I, HasDerivAt A₂ ((-κ) • J₂ t - g.christoffel (γ t) (v t) (A₂ t)) t)
    (h10 : J₁ 0 = 0) (h20 : J₂ 0 = 0) {t : ℝ} (ht : t ∈ I) :
    g.inner (γ t) (J₁ t) (J₂ t) =
      (curvatureSin κ t)^2 * g.inner (γ 0) (A₁ 0) (A₂ 0) := by
  have he := g.parallel_inner_eq hI hdom hγ
    (fun s hs => g.hasDerivAt_oscillatorSecond (hJ₁ s hs) (hA₁ s hs))
    (fun s hs => g.hasDerivAt_oscillatorSecond (hJ₂ s hs) (hA₂ s hs)) h0 ht
  have e1 := g.oscillator_reconstruction κ J₁ A₁ t
  have e2 := g.oscillator_reconstruction κ J₂ A₂ t
  rw [g.oscillator_first_zero hI h0 κ hdom hγ hJ₁ hA₁ h10 ht,smul_zero,zero_add] at e1
  rw [g.oscillator_first_zero hI h0 κ hdom hγ hJ₂ hA₂ h20 ht,smul_zero,zero_add] at e2
  have hz (J A : ℝ → E) : g.oscillatorSecond κ J A 0 = A 0 := by
    simp only [SmoothCoordinateMetric.oscillatorSecond,curvatureSin_zero,curvatureCos_zero,mul_zero,
      zero_smul,one_smul,zero_add]
  rw [hz,hz] at he
  rw [e1,e2]
  simp only [SmoothCoordinateMetric.inner,map_smul,real_inner_smul_left,inner_smul_right] at he ⊢
  rw [he]
  ring

end OAI.Geometry.Nikodym.SmoothCoordinateMetric

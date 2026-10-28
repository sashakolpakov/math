import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ChartRatios
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.LocalizationFlat

/-! # Chart Maps -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ChartMaps

noncomputable section

/-! Projective chart restriction maps as algebras over the original base ring. -/

open _root_.HomogeneousLocalization

universe u v

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

def homogeneousAwayMapBase {f g x : A} {d : ℕ} (hg : g ∈ 𝒜 d) (hx : x = f * g) :
    Away 𝒜 f →ₐ[R] Away 𝒜 x where
  __ := awayMap 𝒜 hg hx
  commutes' r := by
    rw [LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap 𝒜 (Submonoid.powers f),
      LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap 𝒜 (Submonoid.powers x)]
    exact awayMap_fromZeroRingHom 𝒜 hg hx (algebraMap R (𝒜 0) r)

def homogeneousOverlapLeft {s t : A} (ht : t ∈ 𝒜 1) : Away 𝒜 s →ₐ[R] Away 𝒜 (s * t) :=
  homogeneousAwayMapBase 𝒜 ht rfl

def homogeneousOverlapRight {s t : A} (hs : s ∈ 𝒜 1) : Away 𝒜 t →ₐ[R] Away 𝒜 (s * t) :=
  homogeneousAwayMapBase 𝒜 hs (mul_comm s t)

theorem homogeneousOverlapLeft_ratio {s t : A} (hs : s ∈ 𝒜 1) (ht : t ∈ 𝒜 1) (u : 𝒜 1) :
    homogeneousOverlapLeft 𝒜 ht (ChartRatios.degreeOneFraction 𝒜 hs u) = ChartRatios.overlapRatioLeft 𝒜 hs ht u :=
  ChartRatios.awayMap_degreeOneFraction_left 𝒜 hs ht u

theorem homogeneousOverlapRight_ratio {s t : A} (hs : s ∈ 𝒜 1) (ht : t ∈ 𝒜 1) (u : 𝒜 1) :
    homogeneousOverlapRight 𝒜 hs (ChartRatios.degreeOneFraction 𝒜 ht u) = ChartRatios.overlapRatioRight 𝒜 hs ht u :=
  ChartRatios.awayMap_degreeOneFraction_right 𝒜 hs ht u

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ChartMaps

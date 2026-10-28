import OAI.RepresentationTheory.Theta.Adelic.CircleCoordinates
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization
import OAI.RepresentationTheory.Weil.UnitarySplitting.TensorFrameCoordinates

/-! # Circle Coordinate Centralizer -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.CircleCoordinateCentralizer.Inverse

/-! Every native matrix oscillator has an actual trace-tensor preimage.
The coordinate maps preserve operators and identify both symplectic actions. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.TensorFrameCoordinates.Construction OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization.Construction
open OAI.RepresentationTheory.Theta.Adelic.CircleCoordinates

variable {k E : Type} [NormedField k] [NormedField E] [Algebra k E] {n m : ℕ}
variable (σ : E ≃ₐ[k] E) (H : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin m) (Fin m) E)
variable (c : Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame σ H K)

theorem coordinateSymplectic_injective : Function.Injective (CircleCoordinates.coordinateSymplectic σ H K c) := by
  intro a b hab
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply c.coordinates.injective
  have h := congrArg (fun g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k (n * m) => Weil.Local.FunctionsMetaplectic.Construction.symplecticAction g (c.coordinates x)) hab
  simpa only [CircleCoordinates.coordinateSymplectic_apply, c.coordinates.symm_apply_apply] using h

theorem frame_coordinate (a : Weil.UnitarySplitting.Oscillator.Construction.TensorSymplectic σ H K) :
    Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c (Weil.AdelicSplitting.CorrectedNormalization.Construction.standardSymplecticOfMatrix k (n * m) (CircleCoordinates.coordinateSymplectic σ H K c a)) = a := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply c.coordinates.injective
  rw [Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic_coordinates]
  change Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (CircleCoordinates.coordinateSymplectic σ H K c a) (c.coordinates x) = c.coordinates (a.val x)
  rw [CircleCoordinates.coordinateSymplectic_apply, c.coordinates.symm_apply_apply]

theorem coordinate_frame_matrix (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k (n * m)) :
    CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c (Weil.AdelicSplitting.CorrectedNormalization.Construction.standardSymplecticOfMatrix k (n * m) g)) = g := by
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change Weil.Local.FunctionsMetaplectic.Construction.symplecticAction _ x = Weil.Local.FunctionsMetaplectic.Construction.symplecticAction g x
  rw [CircleCoordinates.coordinateSymplectic_apply, Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic_coordinates, c.coordinates.apply_symm_apply]
  rfl

theorem standardToMatrix_injective :
    Function.Injective ((CircleCoordinates.coordinateSymplectic σ H K c).comp (Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c)) :=
  (coordinateSymplectic_injective σ H K c).comp (Weil.UnitarySplitting.TensorFrameCoordinates.Construction.frameSymplectic_injective σ H K c)

variable [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k ℂ)

def tensorCover (b : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ) : Weil.UnitarySplitting.Oscillator.Construction.CircleExtension σ H K c ψ :=
  ⟨(Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c (Weil.AdelicSplitting.CorrectedNormalization.Construction.standardSymplecticOfMatrix k (n * m) b.val.1), b.val.2), b.property.1, by
    intro v f h
    rw [Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic_coordinates]
    exact b.property.2 (c.coordinates v) f h⟩

theorem coordinateCover_tensorCover (b : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ) :
    CircleCoordinates.coordinateCover σ H K c ψ (tensorCover σ H K c ψ b) = b := by
  apply Subtype.ext
  exact Prod.ext (coordinate_frame_matrix σ H K c b.val.1) rfl

theorem coordinateCover_surjective : Function.Surjective (CircleCoordinates.coordinateCover σ H K c ψ) :=
  fun b => ⟨tensorCover σ H K c ψ b, coordinateCover_tensorCover σ H K c ψ b⟩

end RepresentationTheory.Theta.Adelic.CircleCoordinateCentralizer.Inverse

namespace RepresentationTheory.Theta.Adelic.CircleCoordinateCentralizer

/-! Centralizer control for the native oscillator follows from UnitarySplitting's
actual tensor centralizer theorem and the inverse coordinate realization. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.TensorFrameCoordinates.Construction OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization.Construction
open OAI.RepresentationTheory.Theta.Adelic.CircleCoordinates OAI.RepresentationTheory.Theta.Adelic.CircleCoordinateCentralizer.Inverse

variable {k E : Type} [NormedField k] [NormedField E] [Algebra k E] {n m : ℕ}
variable [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
variable (σ : E ≃ₐ[k] E) (H : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin m) (Fin m) E)
variable (c : Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame σ H K) (ψ : AddChar k ℂ)

theorem native_centralizer {G : Type} [Group G]
    (α : G →* Weil.UnitarySplitting.FrameTransport.Construction.StandardSymplectic k (n * m)) (s : G →* Weil.UnitarySplitting.Oscillator.Construction.CircleExtension σ H K c ψ)
    (hs : ∀ (j : Weil.UnitarySplitting.FrameTransport.Construction.StandardSymplectic k (n * m)) (b : Weil.UnitarySplitting.Oscillator.Construction.CircleExtension σ H K c ψ),
      Weil.UnitarySplitting.Oscillator.Construction.circleProjection σ H K c ψ b = Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c j →
      (∀ g, Commute (α g) j) → ∀ g, Commute (s g) b)
    (b : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ)
    (hb : ∀ g, Commute (CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c (α g)))
      (Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ b)) (g : G) :
    Commute (CircleCoordinates.coordinateCover σ H K c ψ (s g)) b := by
  let j := Weil.AdelicSplitting.CorrectedNormalization.Construction.standardSymplecticOfMatrix k (n * m) (Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ b)
  have hcomm (a : G) : Commute (α a) j := by
    change α a * j = j * α a
    apply Inverse.standardToMatrix_injective σ H K c
    rw [map_mul, map_mul]
    change CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c (α a)) *
      CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c j) =
      CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c j) *
        CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c (α a))
    rw [show CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c j) =
      Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ b from Inverse.coordinate_frame_matrix σ H K c _]
    exact (hb a).eq
  have ht := (hs j (Inverse.tensorCover σ H K c ψ b) rfl hcomm g).map (CircleCoordinates.coordinateCover σ H K c ψ)
  rwa [Inverse.coordinateCover_tensorCover] at ht

end RepresentationTheory.Theta.Adelic.CircleCoordinateCentralizer

end

end OAI

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameChartNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.CoordinateProjectivePoints

/-! # Frame Chart Projective Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameChartProjectivePoints

noncomputable section

/-! Every balanced frame chart carries actual projective sections.
Its selected frame is the standard frame as a family of scheme morphisms. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem scalarCoordinateProjectivePoint_congr {S : Scheme.{u}} {n : ℕ}
    {v w : Fin (n + 1) → Γ(S, ⊤)} (hv : ∀ x : S, ∃ i, x ∈ S.basicOpen (v i))
    (hw : ∀ x : S, ∃ i, x ∈ S.basicOpen (w i)) (h : v = w) :
    Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv = Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint w hw := by
  subst w
  rfl

variable (R : Type u) [CommRing R] {n m : ℕ}
variable (i : Fin m) (σ : Fin (n + 1) → Fin m) (e : Fin m) (c : Fin m → Fin (n + 1))
variable (a : (Fin (n + 1) → Fin m) → ℕ) (C : Fin m → (Fin (n + 1) → Fin m) → ℕ)
variable (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
variable (hC : ∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a)

theorem balancedFrameChartProjectiveCoordinates_cover (S : Scheme.{u})
    (ρ : FrameChartCoordinates.balancedDeterminantChartRing R i a ha →+* Γ(S, ⊤)) (z : Fin m) :
    ∀ x : S, ∃ k, x ∈ S.basicOpen (ρ (FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC z k)) := by
  intro x
  refine ⟨c z, ?_⟩
  rw [FrameChartNormalization.balancedFrameChartVectors_selected, map_one]
  exact (S.basicOpen_of_isUnit (isUnit_one : IsUnit (1 : Γ(S, ⊤)))).symm ▸ trivial

def balancedFrameChartProjectivePoint (S : Scheme.{u})
    (ρ : FrameChartCoordinates.balancedDeterminantChartRing R i a ha →+* Γ(S, ⊤)) (z : Fin m) :
    Over.mk (𝟙 S) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n :=
  Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (fun k => ρ (FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC z k))
    (balancedFrameChartProjectiveCoordinates_cover R i σ e c a C ha hC S ρ z)

theorem balancedFrameChartProjectivePoint_normalizes
    (hframe : Frame.ChartDenominators.frameDiscriminantExponent σ e ≤ a) (S : Scheme.{u})
    (ρ : FrameChartCoordinates.balancedDeterminantChartRing R i a ha →+* Γ(S, ⊤)) :
    balancedFrameChartProjectivePoint R i σ e c a C ha hC S ρ e = Scalar.CoordinateProjectivePoints.allOneProjectivePoint S n ∧
      ∀ j, balancedFrameChartProjectivePoint R i σ e c a C ha hC S ρ (σ j) =
        Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint S n j := by
  have hn := FrameChartNormalization.balancedFrameChartVectors_normalizes R i σ e c a C ha hC hframe
  constructor
  · apply scalarCoordinateProjectivePoint_congr
    funext k
    rw [hn.1 k, map_one]
  · intro j
    apply scalarCoordinateProjectivePoint_congr
    funext k
    rw [hn.2 j k]
    by_cases hjk : j = k <;> simp [hjk, Scalar.CoordinateProjectivePoints.standardBasisProjectiveCoordinates]

abbrev balancedFrameChartScheme := Spec (.of (FrameChartCoordinates.balancedDeterminantChartRing R i a ha))

def balancedFrameChartUniversalPoint (z : Fin m) :
    Over.mk (𝟙 (balancedFrameChartScheme R i a ha)) ⟶
      Projective.ProjectivePresentations.projectiveSpaceOver (balancedFrameChartScheme R i a ha) n :=
  balancedFrameChartProjectivePoint R i σ e c a C ha hC (balancedFrameChartScheme R i a ha)
    (Scheme.ΓSpecIso (.of (FrameChartCoordinates.balancedDeterminantChartRing R i a ha))).inv.hom z

theorem balancedFrameChartUniversalPoint_normalizes (hframe : Frame.ChartDenominators.frameDiscriminantExponent σ e ≤ a) :
    balancedFrameChartUniversalPoint R i σ e c a C ha hC e =
        Scalar.CoordinateProjectivePoints.allOneProjectivePoint (balancedFrameChartScheme R i a ha) n ∧
      ∀ j, balancedFrameChartUniversalPoint R i σ e c a C ha hC (σ j) =
        Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint (balancedFrameChartScheme R i a ha) n j :=
  balancedFrameChartProjectivePoint_normalizes R i σ e c a C ha hC hframe _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameChartProjectivePoints

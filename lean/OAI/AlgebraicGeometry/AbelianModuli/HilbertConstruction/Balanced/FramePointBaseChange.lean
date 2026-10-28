import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameChartProjectivePoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.CoordinateProjectiveBaseChange

/-! # Frame Point Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FramePointBaseChange

noncomputable section

/-! The prescribed balanced-frame points are the actual pullbacks of
the universal configuration points on their coefficient chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] {n m : ℕ}
    (i : Fin m) (σ : Fin (n + 1) → Fin m) (e : Fin m) (c : Fin m → Fin (n + 1))
    (a : (Fin (n + 1) → Fin m) → ℕ) (C : Fin m → (Fin (n + 1) → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : ∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a)

theorem balancedFrameChartProjectivePoint_baseChange {S T : Scheme.{u}}
    (ρ : FrameChartCoordinates.balancedDeterminantChartRing R i a ha →+* Γ(S, ⊤)) (f : T ⟶ S) (z : Fin m) :
    Projective.SectionBaseChange.projectiveSectionBaseChange
      (FrameChartProjectivePoints.balancedFrameChartProjectivePoint R i σ e c a C ha hC S ρ z) f =
      FrameChartProjectivePoints.balancedFrameChartProjectivePoint R i σ e c a C ha hC T (f.appTop.hom.comp ρ) z :=
  Scalar.CoordinateProjectiveBaseChange.scalarCoordinateProjectivePoint_baseChange f
    (fun k => ρ (FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC z k))
    (FrameChartProjectivePoints.balancedFrameChartProjectiveCoordinates_cover R i σ e c a C ha hC S ρ z)
    (FrameChartProjectivePoints.balancedFrameChartProjectiveCoordinates_cover R i σ e c a C ha hC T (f.appTop.hom.comp ρ) z)

theorem balancedFrameChartUniversalPoint_baseChange {T : Scheme.{u}}
    (f : T ⟶ FrameChartProjectivePoints.balancedFrameChartScheme R i a ha) (z : Fin m) :
    Projective.SectionBaseChange.projectiveSectionBaseChange (FrameChartProjectivePoints.balancedFrameChartUniversalPoint R i σ e c a C ha hC z) f =
      FrameChartProjectivePoints.balancedFrameChartProjectivePoint R i σ e c a C ha hC T
        (f.appTop.hom.comp (Scheme.ΓSpecIso (.of (FrameChartCoordinates.balancedDeterminantChartRing R i a ha))).inv.hom) z :=
  balancedFrameChartProjectivePoint_baseChange R i σ e c a C ha hC _ f z

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FramePointBaseChange

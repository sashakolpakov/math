import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartTopConstants
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineScalarCocycle
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameRescalingPullback
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalTransitionNormalization

/-! # Normalized Frames -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.NormalizedFrames

noncomputable section

/-! Actual standard-chart frames can be rescaled by field constants
so that their common-point transitions are pure coordinate powers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ}
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n)))

def projectiveNormalizedOpenFrame (i : Fin (n + 1)) :
    (Scheme.Modules.pullback (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)).ι).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)).toScheme :=
  FrameScalarRescaling.rescaleFrame (ChartLineFrames.projectiveOpenLineFrame K i L)
    (Units.map (ChartTopConstants.projectiveChartTopConstants K i).toMonoidHom (LineScalarCocycle.projectiveLineTransitionScalar K L 0 i)⁻¹)

def projectiveNormalizedFieldFrame (i : Fin (n + 1)) :
    (Scheme.Modules.pullback (FunctionFieldPoint.projectiveFunctionFieldPoint K n)).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)))) :=
  FrameAtPoint.frameAtPoint (FieldPointFactors.projectiveCoordinateFieldPoint K i) (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)).ι
    (FunctionFieldPoint.projectiveFunctionFieldPoint K n) (FieldPointFactors.projectiveCoordinateFieldPoint_inclusion K i)
      (projectiveNormalizedOpenFrame K L i)

theorem projectiveNormalizedFieldFrame_eq (i : Fin (n + 1)) :
    projectiveNormalizedFieldFrame K L i = FrameScalarRescaling.rescaleFrame (LineFieldFrames.projectiveLineFieldFrame K L i)
      (Units.map (FieldPointFactors.projectiveCoordinateFieldPoint K i).appTop.hom.toMonoidHom
        (Units.map (ChartTopConstants.projectiveChartTopConstants K i).toMonoidHom (LineScalarCocycle.projectiveLineTransitionScalar K L 0 i)⁻¹)) :=
  FrameRescalingPullback.frameAtPoint_rescale _ _ _ _ _ _

theorem projectiveNormalizedFieldFrame_transition (i j : Fin (n + 1)) :
    (Scheme.ΓSpecIso (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)))).hom
      (FrameTransitionCocycles.frameTransitionValue (projectiveNormalizedFieldFrame K L i) (projectiveNormalizedFieldFrame K L j)) =
        RationalCoordinateDegrees.rationalProjectiveCoordinate i j ^ LineCommonExponent.projectiveLineCommonExponent K L := by
  rw [projectiveNormalizedFieldFrame_eq, projectiveNormalizedFieldFrame_eq,
    FrameScalarRescaling.frameTransitionValue_rescale, map_mul, map_mul]
  have hc (k : Fin (n + 1)) (c : Kˣ) :
      (Scheme.ΓSpecIso (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)))).hom
        ((Units.map (FieldPointFactors.projectiveCoordinateFieldPoint K k).appTop.hom.toMonoidHom
          (Units.map (ChartTopConstants.projectiveChartTopConstants K k).toMonoidHom c) :
            Γ(Spec (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))), ⊤)ˣ) :
              Γ(Spec (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))), ⊤)) =
          algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (C (c : K)) :=
    ChartTopConstants.projectiveCoordinateFieldPoint_constant K k (c : K)
  rw [← map_inv, ← map_inv, inv_inv, hc, hc, ← LineRationalCocycle.projectiveLineTransitionValue_field,
    LineScalarCocycle.projectiveLineTransitionScalar_spec]
  exact RationalTransitionNormalization.rationalProjectiveMonomial_normalize _ _ _ (LineScalarCocycle.projectiveLineTransitionScalar_cocycle K L 0 i j) i j _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.NormalizedFrames

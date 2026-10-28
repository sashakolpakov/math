import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.NormalizedFrames
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapRatioUnits

/-! # Normalized Transitions -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.NormalizedTransitions

noncomputable section

/-! The normalized standard frames have pure coordinate-power
transitions as actual regular functions on each projective overlap. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (K : Type u) [Field K] {n : ℕ}
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n)))

def projectiveNormalizedOverlapLeftFrame (i j : Fin (n + 1)) :
    (Scheme.Modules.pullback (OverlapSectionUnits.projectiveDoubleOpen K i j).ι).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (OverlapSectionUnits.projectiveDoubleOpen K i j).toScheme :=
  Picard.PoincareBundle.Affine.Classification.restrictTrivialization L.sheaf
    ((OverlapSectionUnits.projectiveDoubleOpen_eq_inf K i j).le.trans inf_le_left) (NormalizedFrames.projectiveNormalizedOpenFrame K L i)

def projectiveNormalizedOverlapRightFrame (i j : Fin (n + 1)) :
    (Scheme.Modules.pullback (OverlapSectionUnits.projectiveDoubleOpen K i j).ι).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (OverlapSectionUnits.projectiveDoubleOpen K i j).toScheme :=
  Picard.PoincareBundle.Affine.Classification.restrictTrivialization L.sheaf
    ((OverlapSectionUnits.projectiveDoubleOpen_eq_inf K i j).le.trans inf_le_right) (NormalizedFrames.projectiveNormalizedOpenFrame K L j)

def projectiveNormalizedTransitionValue (i j : Fin (n + 1)) :
    Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j) :=
  (OverlapSectionUnits.projectiveDoubleOpen K i j).topIso.hom
    (FrameTransitionCocycles.frameTransitionValue (projectiveNormalizedOverlapLeftFrame K L i j) (projectiveNormalizedOverlapRightFrame K L i j))

theorem projectiveNormalizedTransitionValue_field (i j : Fin (n + 1)) :
    OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j (projectiveNormalizedTransitionValue K L i j) =
      RationalCoordinateDegrees.rationalProjectiveCoordinate i j ^ LineCommonExponent.projectiveLineCommonExponent K L := by
  have hl := FrameAtPoint.frameAtPoint_restrict ((OverlapSectionUnits.projectiveDoubleOpen_eq_inf K i j).le.trans inf_le_left)
    (FieldPointFactors.projectiveDoubleFieldPoint K i j) (FieldPointFactors.projectiveCoordinateFieldPoint K i) (FunctionFieldPoint.projectiveFunctionFieldPoint K n)
    (FieldPointFactors.projectiveDoubleFieldPoint_inclusion K i j) (FieldPointFactors.projectiveCoordinateFieldPoint_inclusion K i)
    (NormalizedFrames.projectiveNormalizedOpenFrame K L i)
  have hr := FrameAtPoint.frameAtPoint_restrict ((OverlapSectionUnits.projectiveDoubleOpen_eq_inf K i j).le.trans inf_le_right)
    (FieldPointFactors.projectiveDoubleFieldPoint K i j) (FieldPointFactors.projectiveCoordinateFieldPoint K j) (FunctionFieldPoint.projectiveFunctionFieldPoint K n)
    (FieldPointFactors.projectiveDoubleFieldPoint_inclusion K i j) (FieldPointFactors.projectiveCoordinateFieldPoint_inclusion K j)
    (NormalizedFrames.projectiveNormalizedOpenFrame K L j)
  have ht := FrameAtPoint.frameTransitionValue_frameAtPoint (FieldPointFactors.projectiveDoubleFieldPoint K i j) (OverlapSectionUnits.projectiveDoubleOpen K i j).ι
    (FunctionFieldPoint.projectiveFunctionFieldPoint K n) (FieldPointFactors.projectiveDoubleFieldPoint_inclusion K i j)
    (projectiveNormalizedOverlapLeftFrame K L i j) (projectiveNormalizedOverlapRightFrame K L i j)
  change FrameTransitionCocycles.frameTransitionValue
      (FrameAtPoint.frameAtPoint _ _ _ _ (Picard.PoincareBundle.Affine.Classification.restrictTrivialization _ _ _))
      (FrameAtPoint.frameAtPoint _ _ _ _ (Picard.PoincareBundle.Affine.Classification.restrictTrivialization _ _ _)) = _ at ht
  rw [hl, hr] at ht
  have h := congrArg (fun f : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j) ⟶
      CommRingCat.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) =>
        f (projectiveNormalizedTransitionValue K L i j)) (FieldPointFactors.projectiveDoubleFieldPoint_sections K i j)
  change (Scheme.ΓSpecIso (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)))).hom
      ((FieldPointFactors.projectiveDoubleFieldPoint K i j).appTop ((OverlapSectionUnits.projectiveDoubleOpen K i j).topIso.inv
        ((OverlapSectionUnits.projectiveDoubleOpen K i j).topIso.hom
          (FrameTransitionCocycles.frameTransitionValue (projectiveNormalizedOverlapLeftFrame K L i j)
            (projectiveNormalizedOverlapRightFrame K L i j))))) = _ at h
  rw [Iso.hom_inv_id_apply, ← ht] at h
  exact h.symm.trans (NormalizedFrames.projectiveNormalizedFieldFrame_transition K L i j)

theorem projectiveNormalizedTransitionValue_eq_power (i j : Fin (n + 1)) :
    projectiveNormalizedTransitionValue K L i j =
      ((OverlapRatioUnits.projectiveOverlapRatioUnit K i j ^ LineCommonExponent.projectiveLineCommonExponent K L :
        Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j)ˣ) :
          Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j)) := by
  apply Homogeneous.FunctionFieldInjectivity.projectiveOverlapFunctionFieldMap_injective K i j
  rw [projectiveNormalizedTransitionValue_field, OverlapRatioUnits.projectiveOverlapRatioUnit_field_zpow]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.NormalizedTransitions

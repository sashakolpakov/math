import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineFieldFrames
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapRationalMonomials
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FrameExponents

/-! # Line Rational Cocycle -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineRationalCocycle

noncomputable section

/-! Actual line-bundle transitions satisfy the common-field cocycle.
Consequently their canonical coordinate exponents agree on every triple. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (K : Type u) [Field K] {n : ℕ}
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n)))

theorem projectiveLineTransitionValue_field (i j : Fin (n + 1)) :
    OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j (LineTransitionPowers.projectiveLineTransitionValue K L i j) =
      (Scheme.ΓSpecIso (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)))).hom
        (FrameTransitionCocycles.frameTransitionValue (LineFieldFrames.projectiveLineFieldFrame K L i) (LineFieldFrames.projectiveLineFieldFrame K L j)) := by
  have h := congrArg (fun f : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j) ⟶
      CommRingCat.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) =>
        f (LineTransitionPowers.projectiveLineTransitionValue K L i j)) (FieldPointFactors.projectiveDoubleFieldPoint_sections K i j)
  change (Scheme.ΓSpecIso (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)))).hom
      ((FieldPointFactors.projectiveDoubleFieldPoint K i j).appTop
        ((OverlapSectionUnits.projectiveDoubleOpen K i j).topIso.inv ((OverlapSectionUnits.projectiveDoubleOpen K i j).topIso.hom
          (FrameTransitionCocycles.frameTransitionValue (LineTransitionPowers.projectiveLineOverlapLeftFrame K L i j)
            (LineTransitionPowers.projectiveLineOverlapRightFrame K L i j))))) = _ at h
  rw [Iso.hom_inv_id_apply, ← LineFieldFrames.projectiveLineFieldFrame_transition] at h
  exact h.symm

theorem projectiveLineTransitionValue_rational_cocycle (i j k : Fin (n + 1)) :
    OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j (LineTransitionPowers.projectiveLineTransitionValue K L i j) *
      OverlapFunctionField.projectiveOverlapFunctionFieldMap K j k (LineTransitionPowers.projectiveLineTransitionValue K L j k) =
        OverlapFunctionField.projectiveOverlapFunctionFieldMap K i k (LineTransitionPowers.projectiveLineTransitionValue K L i k) := by
  rw [projectiveLineTransitionValue_field, projectiveLineTransitionValue_field,
    projectiveLineTransitionValue_field, ← map_mul, FrameTransitionCocycles.frameTransitionValue_cocycle]

theorem projectiveLineTransitionExponent_triple (i j k : Fin (n + 1))
    (hji : j ≠ i) (hkj : k ≠ j) (hki : k ≠ i) :
    FrameExponents.projectiveLineTransitionExponent K i j hji L = FrameExponents.projectiveLineTransitionExponent K j k hkj L ∧
      FrameExponents.projectiveLineTransitionExponent K j k hkj L = FrameExponents.projectiveLineTransitionExponent K i k hki L := by
  apply OverlapRationalMonomials.projectiveOverlap_exponents_of_functionField_cocycle
  change OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j (LineTransitionPowers.projectiveLineTransitionValue_isUnit K L i j).unit.val *
      OverlapFunctionField.projectiveOverlapFunctionFieldMap K j k (LineTransitionPowers.projectiveLineTransitionValue_isUnit K L j k).unit.val =
        OverlapFunctionField.projectiveOverlapFunctionFieldMap K i k (LineTransitionPowers.projectiveLineTransitionValue_isUnit K L i k).unit.val
  rw [(LineTransitionPowers.projectiveLineTransitionValue_isUnit K L i j).unit_spec,
    (LineTransitionPowers.projectiveLineTransitionValue_isUnit K L j k).unit_spec,
    (LineTransitionPowers.projectiveLineTransitionValue_isUnit K L i k).unit_spec]
  exact projectiveLineTransitionValue_rational_cocycle K L i j k

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineRationalCocycle

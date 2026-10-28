import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapExponents
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameTransitionCocycles
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineTransitionPowers

/-! # Frame Exponents -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FrameExponents

noncomputable section

/-! Standard-overlap frame transitions have canonical integer
exponents, with an exact cocycle law and explicit scalar-power evaluation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (K : Type u) [Field K] {n : ℕ} (i j : Fin (n + 1)) (hji : j ≠ i)
variable {M : (OverlapSectionUnits.projectiveDoubleOpen K i j).toScheme.Modules}

def projectiveOverlapFrameExponent (e f : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (OverlapSectionUnits.projectiveDoubleOpen K i j).toScheme) : ℤ :=
  OverlapExponents.projectiveOverlapUnitExponent K i j hji
    (Units.map (OverlapSectionUnits.projectiveDoubleOpen K i j).topIso.hom.hom.toMonoidHom (FrameTransitionCocycles.frameTransitionUnit e f))

theorem projectiveOverlapFrameExponent_cocycle
    (e f g : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (OverlapSectionUnits.projectiveDoubleOpen K i j).toScheme) :
    projectiveOverlapFrameExponent K i j hji e f + projectiveOverlapFrameExponent K i j hji f g =
      projectiveOverlapFrameExponent K i j hji e g := by
  unfold projectiveOverlapFrameExponent
  rw [← OverlapExponents.projectiveOverlapUnitExponent_mul, ← map_mul, FrameTransitionCocycles.frameTransitionUnit_cocycle]

def projectiveLineTransitionExponent (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n))) : ℤ :=
  OverlapExponents.projectiveOverlapUnitExponent K i j hji (LineTransitionPowers.projectiveLineTransitionUnit K L i j)

theorem projectiveLineTransitionExponent_of_equation
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n))) (c : Kˣ) (a b : ℕ)
    (h : LineTransitionPowers.projectiveLineTransitionValue K L i j * OverlapSectionUnits.projectiveOverlapRatio K i j ^ b =
      OverlapSectionUnits.projectiveOverlapConstant K i j (c : K) * OverlapSectionUnits.projectiveOverlapRatio K i j ^ a) :
    projectiveLineTransitionExponent K i j hji L = (a : ℤ) - b := by
  apply OverlapExponents.projectiveOverlapUnitExponent_of_equation K i j hji _ c a b
  change (LineTransitionPowers.projectiveLineTransitionValue_isUnit K L i j).unit.val * OverlapSectionUnits.projectiveOverlapRatio K i j ^ b = _
  rw [(LineTransitionPowers.projectiveLineTransitionValue_isUnit K L i j).unit_spec]
  exact h

theorem projectiveLineTransitionExponent_eq_frame
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n))) :
    projectiveLineTransitionExponent K i j hji L =
      projectiveOverlapFrameExponent K i j hji
        (LineTransitionPowers.projectiveLineOverlapLeftFrame K L i j) (LineTransitionPowers.projectiveLineOverlapRightFrame K L i j) := by
  apply congrArg (OverlapExponents.projectiveOverlapUnitExponent K i j hji)
  apply Units.ext
  change (LineTransitionPowers.projectiveLineTransitionValue_isUnit K L i j).unit.val =
    (OverlapSectionUnits.projectiveDoubleOpen K i j).topIso.hom
      (FrameTransitionCocycles.frameTransitionValue_isUnit (LineTransitionPowers.projectiveLineOverlapLeftFrame K L i j)
        (LineTransitionPowers.projectiveLineOverlapRightFrame K L i j)).unit.val
  rw [(LineTransitionPowers.projectiveLineTransitionValue_isUnit K L i j).unit_spec,
    (FrameTransitionCocycles.frameTransitionValue_isUnit (LineTransitionPowers.projectiveLineOverlapLeftFrame K L i j)
      (LineTransitionPowers.projectiveLineOverlapRightFrame K L i j)).unit_spec]
  rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FrameExponents

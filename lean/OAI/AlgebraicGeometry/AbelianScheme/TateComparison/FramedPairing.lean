import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitPairing
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BilinearBaseChange

/-! # Framed Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual action-compatible Tate frame transports a Rosati form
to the required nondegenerate pairings of chosen and opposite blocks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  {S : Scheme} (P : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S)
  (T : Over S) (e : Rational.SplitTateFrame s P.abelian.scheme T q)
  (he : Rational.IsSplitActionFrame P T q D.localCharacter e)
  (B : LinearMap.BilinForm ℚ_[q] (Rational.rationalTateModule P.abelian.scheme T q))

include hg he in
theorem Data.SphericalPELAlbaneseData.framedPairing_balanced
    (hB : ∀ (a : NumberField.RingOfIntegers E) x y,
      B (Rational.rationalTateMap (T := T) (q := q)
        (End.endSchemeMap P.abelian.scheme (P.action (NumberField.IsCMField.ringOfIntegersComplexConj E a))) x) y =
      B x (Rational.rationalTateMap (T := T) (q := q) (End.endSchemeMap P.abelian.scheme (P.action a)) y))
    (a : NumberField.RingOfIntegers E) (x y : Rational.SplitTateSpace s q) :
    LinearMap.BilinForm.congr e B
      (SplitPairing.coordinateScalarMap (fun i => (D.localCharacter (Data.SphericalPELAlbaneseData.oppositeBlock i) a : ℚ_[q])) x) y =
      LinearMap.BilinForm.congr e B x
        (SplitPairing.coordinateScalarMap (fun i => (D.localCharacter i a : ℚ_[q])) y) := by
  apply BilinearBaseChange.bilinearCongr_adjoint B e
    (Rational.rationalTateMap (T := T) (q := q)
      (End.endSchemeMap P.abelian.scheme (P.action (NumberField.IsCMField.ringOfIntegersComplexConj E a))))
    (Rational.rationalTateMap (T := T) (q := q) (End.endSchemeMap P.abelian.scheme (P.action a))) _ _
  · apply LinearMap.ext
    intro z
    funext v i
    change (D.localCharacter (v.1, !v.2) a : ℚ_[q]) * e z v i = _
    rw [hg.2.1 v.1 v.2 a]
    exact (he (NumberField.IsCMField.ringOfIntegersComplexConj E a) z v i).symm
  · apply LinearMap.ext
    intro z
    funext v i
    exact (he a z v i).symm
  · exact hB a

def Data.SphericalPELAlbaneseData.framedOppositePairing (v : Fin s) : LinearMap.BilinForm ℚ_[q] (Fin 3 → ℚ_[q]) :=
  PairedBlocks.oppositeBlockPairing (LinearMap.BilinForm.congr e B) Data.SphericalPELAlbaneseData.oppositeBlock (v, false)

include hg he in
theorem Data.SphericalPELAlbaneseData.framedOppositePairing_nondegenerate (hB : B.Nondegenerate)
    (hRosati : ∀ (a : NumberField.RingOfIntegers E) x y,
      B (Rational.rationalTateMap (T := T) (q := q)
        (End.endSchemeMap P.abelian.scheme (P.action (NumberField.IsCMField.ringOfIntegersComplexConj E a))) x) y =
      B x (Rational.rationalTateMap (T := T) (q := q) (End.endSchemeMap P.abelian.scheme (P.action a)) y))
    (v : Fin s) : (D.framedOppositePairing P T e B v).Nondegenerate :=
  D.splitPairing_block_nondegenerate hg (LinearMap.BilinForm.congr e B) (hB.congr e)
    (D.framedPairing_balanced hg P T e he B hRosati) (v, false)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison

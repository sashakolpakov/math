import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELWeilAdjointTransport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELWeilSelfDuality
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FramedPairing

/-! # Geometric Weil Balance -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! IntegralModel classification supplies Rosati balance for the actual Weil
Tate pairing on every geometric fiber and in every compatible frame. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hgeometry : D.HasIntegralModelGeometry) {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b)

theorem Data.SphericalPELAlbaneseData.geometricRationalWeilPairing_adjoint (a : NumberField.RingOfIntegers E)
    (v w : Rational.rationalTateModule (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :
    D.geometricRationalWeilPairing hg hgeometry b x
        (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
          (End.endSchemeMap (D.fiberFamily b x).abelian.scheme ((D.fiberFamily b x).action a)) v) w =
      D.geometricRationalWeilPairing hg hgeometry b x v
        (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
          (End.endSchemeMap (D.fiberFamily b x).abelian.scheme
            ((D.fiberFamily b x).action (NumberField.IsCMField.ringOfIntegersComplexConj E a))) w) := by
  have : IsReduced (Over.mk (b ≫ D.generic)).left := inferInstanceAs (IsReduced (Spec (.of k)))
  have hp := (hgeometry.classifies.1 (Over.mk (b ≫ D.generic)) (D.modelGeometricPoint b x)).1
  let e := D.model.family.pullbackComp (pullback.fst D.model.space.hom D.generic) x.left
  exact e.rationalWeil_adjoint D.reference.polarizationType
    (D.fiberPolarizationType hgeometry b x) hp.1 hg.2.2.2.2
    (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom hp.2.2 a v w

theorem Data.SphericalPELAlbaneseData.geometricRationalWeilPairing_rosati (a : NumberField.RingOfIntegers E)
    (v w : Rational.rationalTateModule (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :
    D.geometricRationalWeilPairing hg hgeometry b x
        (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
          (End.endSchemeMap (D.fiberFamily b x).abelian.scheme
            ((D.fiberFamily b x).action (NumberField.IsCMField.ringOfIntegersComplexConj E a))) v) w =
      D.geometricRationalWeilPairing hg hgeometry b x v
        (Rational.rationalTateMap (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
          (End.endSchemeMap (D.fiberFamily b x).abelian.scheme ((D.fiberFamily b x).action a)) w) := by
  have hc : NumberField.IsCMField.ringOfIntegersComplexConj E
      (NumberField.IsCMField.ringOfIntegersComplexConj E a) = a := by
    apply NumberField.RingOfIntegers.ext
    change NumberField.IsCMField.complexConj E (NumberField.IsCMField.complexConj E (a : E)) = (a : E)
    exact NumberField.IsCMField.complexConj_apply_apply E _
  simpa only [hc] using
    D.geometricRationalWeilPairing_adjoint hg hgeometry b x
      (NumberField.IsCMField.ringOfIntegersComplexConj E a) v w

variable (frame : D.FiberFrame b x)
  (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)

include hf in
theorem Data.SphericalPELAlbaneseData.geometricWeilFrame_orthogonal (i j : Fin s × Bool) (hij : i ≠ Data.SphericalPELAlbaneseData.oppositeBlock j)
    (v w : Fin 3 → ℚ_[q]) :
    LinearMap.BilinForm.congr frame (D.geometricRationalWeilPairing hg hgeometry b x)
      (Pi.single i v) (Pi.single j w) = 0 :=
  SplitPairing.balanced_blocks_orthogonal _ Data.SphericalPELAlbaneseData.oppositeBlock Data.SphericalPELAlbaneseData.oppositeBlock_involutive
    (fun a i => (D.localCharacter i a : ℚ_[q]))
    (fun _ _ hij => D.rationalCharacter_separates hg hij)
    (D.framedPairing_balanced hg (D.fiberFamily b x) _ frame hf
      (D.geometricRationalWeilPairing hg hgeometry b x)
      (D.geometricRationalWeilPairing_rosati hg hgeometry b x)) i j hij v w

include hf in
theorem Data.SphericalPELAlbaneseData.geometricWeilOppositePairing_nondegenerate (v : Fin s) :
    (D.framedOppositePairing (D.fiberFamily b x) _ frame
      (D.geometricRationalWeilPairing hg hgeometry b x) v).Nondegenerate :=
  D.framedOppositePairing_nondegenerate hg (D.fiberFamily b x) _ frame hf
    (D.geometricRationalWeilPairing hg hgeometry b x)
    (D.geometricRationalWeilPairing_nondegenerate hg hgeometry b x)
    (D.geometricRationalWeilPairing_rosati hg hgeometry b x) v

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison

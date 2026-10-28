import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELPerfectPairing
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PerfectPairingScalarExtension

/-! # PEL Weil Self Duality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual geometric PEL polarization gives a nondegenerate
rational Tate pairing with precisely self-dual integral Tate lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hgeometry : D.HasIntegralModelGeometry) {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b)

def Data.SphericalPELAlbaneseData.geometricRationalWeilPairing :
    LinearMap.BilinForm ℚ_[q]
      (Rational.rationalTateModule (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :=
  LinearMap.BilinForm.baseChange ℚ_[q] (D.geometricTateWeilPairing hg hgeometry b x)

theorem Data.SphericalPELAlbaneseData.geometricRationalWeilPairing_nondegenerate :
    (D.geometricRationalWeilPairing hg hgeometry b x).Nondegenerate :=
  PerfectPairingScalarExtension.perfectBilinearBaseChange_nondegenerate (GeometricLattice.geometricTateBasis (D.fiberFamily b x).abelian q)
    (D.geometricTateWeilPairing hg hgeometry b x) (D.geometricTateWeilPairing_isPerfect hg hgeometry b x)

theorem Data.SphericalPELAlbaneseData.geometricRationalWeilPairing_self_dual :
    (D.geometricRationalWeilPairing hg hgeometry b x).dualSubmodule
        (Rational.integralTateImage (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) =
      Rational.integralTateImage (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q :=
  PerfectPairingScalarExtension.tensorIntegralImage_self_dual (GeometricLattice.geometricTateBasis (D.fiberFamily b x).abelian q)
    (D.geometricTateWeilPairing hg hgeometry b x) (D.geometricTateWeilPairing_isPerfect hg hgeometry b x)
    (Isogeny.Tate.integralEmbedding_injective q)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison

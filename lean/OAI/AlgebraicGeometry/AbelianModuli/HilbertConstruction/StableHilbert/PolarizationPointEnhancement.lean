import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EnhancementParameterPullback

/-! # Polarization Point Enhancement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationPointEnhancement

noncomputable section

/-! The original universal polarization enhancement at an arbitrary
parameter point, with its actual full-level pullback comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private def originalEnhancementAtIso
    {R : Type} [CommRing R] [IsNoetherianRing R]
    (M : Over (Spec (.of R))) [IsNoetherian M.left] {g N : ℕ}
    (F : Level.Data.AbelianSchemeWithFullLevel g N M.left) (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (qS : M.left ⟶ Spec (.of ℚ)) (d : ℕ) (hd : 0 < d)
    (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k) {T : Over (Spec (.of R))}
    (z : T ⟶ Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.parameter M F P qS d hd δ hδ) :
    Moduli.Isomorphisms.LevelPreservingIso
      ((Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.universalFamily M F P qS d hd δ hδ).pullback z.left)
      (Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.enhancementAt M F P qS d hd δ hδ z).object := by
  let c : Over.mk (z ≫ Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.inclusion M F P qS d hd δ hδ).left ⟶
      Over.mk (Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.inclusion M F P qS d hd δ hδ).left :=
    Over.homMk z.left rfl
  exact GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement.parameterPullbackModuliIso
    (F := F) (L := F.abelian.zeroNormalizedBundle P.ampleLineBundle)
    (T := Over.mk (Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.inclusion M F P qS d hd δ hδ).left)
    (U := Over.mk (z ≫ Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.inclusion M F P qS d hd δ hδ).left)
    (Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.universalEnhancement M F P qS d hd δ hδ) c

namespace StableHilbertPolarization
variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)
    {T : Over (Spec (.of R))}
    (z : T ⟶ PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ)

def pointEnhancement : GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
    (LevelComparison.StableHilbertLevelComparison.familyAt R i D H hH g Hm Hi N labels j (z ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ)))
    (LevelComparison.StableHilbertLevelComparison.lineAt R i D H hH g Hm Hi N labels j (z ≫ (PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ))) d :=
  Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.enhancementAt (PolarizationParameter.StableHilbertPolarization.base R i j D H hH g Hm Hi N labels) (PolarizationParameter.StableHilbertPolarization.baseFamily R i j D H hH g Hm Hi N labels) (PolarizationParameter.StableHilbertPolarization.basePresentation R i j D H hH g Hm Hi N labels) (((PolarizationParameter.StableHilbertPolarization.base R i j D H hH g Hm Hi N labels)).hom ≫ qR) d hd δ hδ z

def pointEnhancementIso :
    Moduli.Isomorphisms.LevelPreservingIso ((PolarizationParameter.StableHilbertPolarization.universalFamily R i j D H hH g Hm Hi N labels qR d hd δ hδ).pullback z.left)
      (pointEnhancement R i D H hH g Hm Hi N labels qR d hd δ hδ j z).object := by
  exact originalEnhancementAtIso (PolarizationParameter.StableHilbertPolarization.base R i j D H hH g Hm Hi N labels) (PolarizationParameter.StableHilbertPolarization.baseFamily R i j D H hH g Hm Hi N labels) (PolarizationParameter.StableHilbertPolarization.basePresentation R i j D H hH g Hm Hi N labels) (((PolarizationParameter.StableHilbertPolarization.base R i j D H hH g Hm Hi N labels)).hom ≫ qR) d hd δ hδ z

end StableHilbertPolarization

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationPointEnhancement

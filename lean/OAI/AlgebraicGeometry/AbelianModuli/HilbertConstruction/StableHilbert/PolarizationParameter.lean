import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.GlobalGraphPowerParameter

/-! # Polarization Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization

noncomputable section

/-! The constructed normalized polarization locus on an actual stable
Hilbert full-level chart. This adapter retains the original marked
family and projective presentation; it makes no fine-moduli claim. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))

abbrev base : Over (Spec (.of R)) :=
  LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels

abbrev baseFamily : Level.Data.AbelianSchemeWithFullLevel g N
    (base R i j D H hH g Hm Hi N labels).left :=
  LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels

abbrev basePresentation : Projective.ProjectivePresentations.ProjectivePresentation
    (baseFamily R i j D H hH g Hm Hi N labels).abelian.scheme :=
  LevelParameter.StableHilbertLevel.presentation R i j D H hH g Hm Hi N labels

def baseQuasiProjective :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (base R i j D H hH g Hm Hi N labels) :=
  LevelParameter.StableHilbertLevel.quasiProjective R i j D H hH g Hm Hi N labels

instance base_noetherian : IsNoetherian (base R i j D H hH g Hm Hi N labels).left :=
  (baseQuasiProjective R i j D H hH g Hm Hi N labels).noetherian

variable (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)

def parameter : Over (Spec (.of R)) :=
  Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.parameter (base R i j D H hH g Hm Hi N labels)
    (baseFamily R i j D H hH g Hm Hi N labels)
    (basePresentation R i j D H hH g Hm Hi N labels)
    ((base R i j D H hH g Hm Hi N labels).hom ≫ qR) d hd δ hδ

def inclusion : parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ ⟶
    base R i j D H hH g Hm Hi N labels :=
  Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.inclusion (base R i j D H hH g Hm Hi N labels)
    (baseFamily R i j D H hH g Hm Hi N labels)
    (basePresentation R i j D H hH g Hm Hi N labels)
    ((base R i j D H hH g Hm Hi N labels).hom ≫ qR) d hd δ hδ

instance inclusion_left_mono : Mono (inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ).left :=
  Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.inclusion_left_mono _ _ _ _ _ _ _ _

instance inclusion_mono : Mono (inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ) :=
  Over.mono_of_mono_left _

instance inclusion_locallyOfFiniteType :
    LocallyOfFiniteType (inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ).left :=
  Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.inclusion_locallyOfFiniteType _ _ _ _ _ _ _ _

instance inclusion_quasiCompact :
    QuasiCompact (inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ).left :=
  Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.inclusion_quasiCompact _ _ _ _ _ _ _ _

def quasiProjective :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ) :=
  Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.quasiProjectivePresentation
    (base R i j D H hH g Hm Hi N labels)
    (baseFamily R i j D H hH g Hm Hi N labels)
    (basePresentation R i j D H hH g Hm Hi N labels)
    ((base R i j D H hH g Hm Hi N labels).hom ≫ qR) d hd δ hδ
    (baseQuasiProjective R i j D H hH g Hm Hi N labels)

def universalFamily : PolarizationData.PolarizedAbelianWithFullLevel g δ N
    (parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ).left :=
  Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.universalFamily
    (base R i j D H hH g Hm Hi N labels)
    (baseFamily R i j D H hH g Hm Hi N labels)
    (basePresentation R i j D H hH g Hm Hi N labels)
    ((base R i j D H hH g Hm Hi N labels).hom ≫ qR) d hd δ hδ

theorem universalFamily_abelian :
    (universalFamily R i j D H hH g Hm Hi N labels qR d hd δ hδ).abelian =
      (baseFamily R i j D H hH g Hm Hi N labels).abelian.pullback
        (inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ).left := rfl

theorem universalFamily_level :
    (universalFamily R i j D H hH g Hm Hi N labels qR d hd δ hδ).level =
      (baseFamily R i j D H hH g Hm Hi N labels).level.pullback
        (inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ).left := rfl

def universalPresentation : Projective.ProjectivePresentations.ProjectivePresentation
    (universalFamily R i j D H hH g Hm Hi N labels qR d hd δ hδ).abelian.scheme :=
  (basePresentation R i j D H hH g Hm Hi N labels).baseChange
    (inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ).left

/-- The all-test condition concerns the original stable marked family. -/
theorem lifts_iff (T : Over (Spec (.of R)))
    (x : T ⟶ base R i j D H hH g Hm Hi N labels) :
    (∃ z : T ⟶ parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ,
      z ≫ inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ = x) ↔
      Nonempty (GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
        ((baseFamily R i j D H hH g Hm Hi N labels).pullback x.left)
        (((baseFamily R i j D H hH g Hm Hi N labels).abelian.zeroNormalizedBundle
          (basePresentation R i j D H hH g Hm Hi N labels).ampleLineBundle).pullback
            (pullback.fst (baseFamily R i j D H hH g Hm Hi N labels).abelian.scheme.hom x.left)) d) :=
  Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.lifts_iff (base R i j D H hH g Hm Hi N labels)
    (baseFamily R i j D H hH g Hm Hi N labels)
    (basePresentation R i j D H hH g Hm Hi N labels)
    ((base R i j D H hH g Hm Hi N labels).hom ≫ qR) d hd δ hδ T x

theorem existsUnique_lift_iff (T : Over (Spec (.of R)))
    (x : T ⟶ base R i j D H hH g Hm Hi N labels) :
    (∃! z : T ⟶ parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ,
      z ≫ inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ = x) ↔
      Nonempty (GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
        ((baseFamily R i j D H hH g Hm Hi N labels).pullback x.left)
        (((baseFamily R i j D H hH g Hm Hi N labels).abelian.zeroNormalizedBundle
          (basePresentation R i j D H hH g Hm Hi N labels).ampleLineBundle).pullback
            (pullback.fst (baseFamily R i j D H hH g Hm Hi N labels).abelian.scheme.hom x.left)) d) := by
  constructor
  · intro h
    exact (lifts_iff R i j D H hH g Hm Hi N labels qR d hd δ hδ T x).mp h.exists
  · intro h
    obtain ⟨z, hz⟩ := (lifts_iff R i j D H hH g Hm Hi N labels qR d hd δ hδ T x).mpr h
    refine ⟨z, hz, fun y hy => ?_⟩
    exact (cancel_mono (inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ)).mp
      (hy.trans hz.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization

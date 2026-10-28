import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.LocusPresentation

/-! # Graph Power Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower

noncomputable section

/-! Stable Hilbert polarization charts from actual presentations of
the graph-power locus over an arbitrary Noetherian affine base. -/

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

def baseQuasiProjective : Projective.ProjectivePresentations.QuasiProjectivePresentation
    (base R i j D H hH g Hm Hi N labels) :=
  LevelParameter.StableHilbertLevel.quasiProjective R i j D H hH g Hm Hi N labels

instance base_noetherian : IsNoetherian
    (base R i j D H hH g Hm Hi N labels).left :=
  (baseQuasiProjective R i j D H hH g Hm Hi N labels).noetherian

variable (d : ℕ) (δ : Fin g → ℕ) (Φ : GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ)

def locus : GraphPower.LocusPresentation.GraphPowerLocusPresentation
    (base R i j D H hH g Hm Hi N labels)
    (baseFamily R i j D H hH g Hm Hi N labels)
    (basePresentation R i j D H hH g Hm Hi N labels) d δ :=
  Φ (base R i j D H hH g Hm Hi N labels)
    (baseFamily R i j D H hH g Hm Hi N labels)
    (basePresentation R i j D H hH g Hm Hi N labels)

def parameter : Over (Spec (.of R)) :=
  (locus R i j D H hH g Hm Hi N labels d δ Φ).parameter

def inclusion : StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ ⟶
    base R i j D H hH g Hm Hi N labels :=
  (locus R i j D H hH g Hm Hi N labels d δ Φ).inclusion

instance inclusion_left_mono :
    Mono (StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ).left :=
  (locus R i j D H hH g Hm Hi N labels d δ Φ).inclusion_left_mono

instance inclusion_mono :
    Mono (StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ) :=
  Over.mono_of_mono_left _

instance inclusion_locallyOfFiniteType :
    LocallyOfFiniteType (StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ).left :=
  (locus R i j D H hH g Hm Hi N labels d δ Φ).inclusion_locallyOfFiniteType

instance inclusion_quasiCompact :
    QuasiCompact (StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ).left :=
  (locus R i j D H hH g Hm Hi N labels d δ Φ).inclusion_quasiCompact

def quasiProjective : Projective.ProjectivePresentations.QuasiProjectivePresentation
    (StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ) :=
  (locus R i j D H hH g Hm Hi N labels d δ Φ).quasiProjective
    (baseQuasiProjective R i j D H hH g Hm Hi N labels)

instance parameter_noetherian :
    IsNoetherian (StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ).left :=
  (StableHilbertGraphPower.quasiProjective R i j D H hH g Hm Hi N labels d δ Φ).noetherian

def universalFamily : PolarizationData.PolarizedAbelianWithFullLevel g δ N
    (StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ).left :=
  (locus R i j D H hH g Hm Hi N labels d δ Φ).universalFamily

theorem universalFamily_abelian :
    (StableHilbertGraphPower.universalFamily R i j D H hH g Hm Hi N labels d δ Φ).abelian =
      (baseFamily R i j D H hH g Hm Hi N labels).abelian.pullback
        (StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ).left := rfl

theorem universalFamily_level :
    (StableHilbertGraphPower.universalFamily R i j D H hH g Hm Hi N labels d δ Φ).level =
      (baseFamily R i j D H hH g Hm Hi N labels).level.pullback
        (StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ).left := rfl

def universalPresentation : Projective.ProjectivePresentations.ProjectivePresentation
    (StableHilbertGraphPower.universalFamily R i j D H hH g Hm Hi N labels d δ Φ).abelian.scheme :=
  (basePresentation R i j D H hH g Hm Hi N labels).baseChange
    (StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ).left

theorem lifts_iff (T : Over (Spec (.of R)))
    (x : T ⟶ base R i j D H hH g Hm Hi N labels) :
    (∃ z : T ⟶ StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ,
      z ≫ StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ = x) ↔
      Nonempty (GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
        ((baseFamily R i j D H hH g Hm Hi N labels).pullback x.left)
        (((baseFamily R i j D H hH g Hm Hi N labels).abelian.zeroNormalizedBundle
          (basePresentation R i j D H hH g Hm Hi N labels).ampleLineBundle).pullback
            (pullback.fst (baseFamily R i j D H hH g Hm Hi N labels).abelian.scheme.hom x.left)) d) :=
  (locus R i j D H hH g Hm Hi N labels d δ Φ).lifts_iff T x

theorem existsUnique_lift_iff (T : Over (Spec (.of R)))
    (x : T ⟶ base R i j D H hH g Hm Hi N labels) :
    (∃! z : T ⟶ StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ,
      z ≫ StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ = x) ↔
      Nonempty (GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
        ((baseFamily R i j D H hH g Hm Hi N labels).pullback x.left)
        (((baseFamily R i j D H hH g Hm Hi N labels).abelian.zeroNormalizedBundle
          (basePresentation R i j D H hH g Hm Hi N labels).ampleLineBundle).pullback
            (pullback.fst (baseFamily R i j D H hH g Hm Hi N labels).abelian.scheme.hom x.left)) d) :=
  (locus R i j D H hH g Hm Hi N labels d δ Φ).existsUnique_lift_iff T x

def pointEnhancement {T : Over (Spec (.of R))}
    (z : T ⟶ StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ) :
    GraphPower.PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ
      ((baseFamily R i j D H hH g Hm Hi N labels).pullback
        (z ≫ StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ).left)
      (((baseFamily R i j D H hH g Hm Hi N labels).abelian.zeroNormalizedBundle
        (basePresentation R i j D H hH g Hm Hi N labels).ampleLineBundle).pullback
        (pullback.fst (baseFamily R i j D H hH g Hm Hi N labels).abelian.scheme.hom
          (z ≫ StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ).left)) d :=
  (locus R i j D H hH g Hm Hi N labels d δ Φ).enhancementAt z

def pointEnhancementIso {T : Over (Spec (.of R))}
    (z : T ⟶ StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ) :
    Moduli.Isomorphisms.LevelPreservingIso
      ((StableHilbertGraphPower.universalFamily R i j D H hH g Hm Hi N labels d δ Φ).pullback z.left)
      (pointEnhancement R i j D H hH g Hm Hi N labels d δ Φ z).object :=
  (locus R i j D H hH g Hm Hi N labels d δ Φ).enhancementAtIso z

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower

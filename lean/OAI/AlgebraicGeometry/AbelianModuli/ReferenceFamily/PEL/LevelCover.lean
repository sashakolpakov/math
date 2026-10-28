import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AddedPEL
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.CoverIs

/-! # Level Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL

noncomputable section

/-! The added-level parameter scheme carries the actual pulled-back
PEL family with both the prescribed and auxiliary markings. Forgetting
the auxiliary marking recovers the prescribed family exactly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N L : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
  {T : Over (Spec (.of K))}

variable (A : Objects.PELObject P iota N T) [NeZero L]

def Objects.PELObject.auxiliaryLevelScheme : Over (Spec (.of K)) :=
  (Over.map T.hom).obj (Frame.Locus.LevelCover.fullFrameScheme A.polarized.abelian T.hom (N := L))

def Objects.PELObject.auxiliaryLevelProjection : Objects.PELObject.auxiliaryLevelScheme A (L := L) ⟶ T :=
  Over.homMk (Frame.Locus.LevelCover.fullFrameScheme A.polarized.abelian T.hom (N := L)).hom rfl

def Objects.PELObject.universalAddedLevel : AddedPEL.AddedPELLevel P iota L N (Objects.PELObject.auxiliaryLevelScheme A (L := L)) :=
  AddedPEL.AddedPELLevel.ofPrescribed (A.pullback (Objects.PELObject.auxiliaryLevelProjection A))
    (Finite.Monomorphisms.LevelCover.canonicalFullFrameLevel A.polarized.abelian T.hom)

theorem Objects.PELObject.universalAddedLevel_forget :
    (Objects.PELObject.universalAddedLevel A (L := L)).forgetAuxiliary = A.pullback (Objects.PELObject.auxiliaryLevelProjection A) := rfl

/-- The auxiliary-level family is linked to the original PEL object
by the exact scheme-theoretic pullback comparison used by IsFine. -/
def Objects.PELObject.universalAddedLevel_comparison :
    Models.PELPullbackIso A (Objects.PELObject.universalAddedLevel A (L := L)).forgetAuxiliary (Objects.PELObject.auxiliaryLevelProjection A) :=
  Models.PELPullbackIso.canonical A (Objects.PELObject.auxiliaryLevelProjection A)

theorem Objects.PELObject.auxiliaryLevelProjection_finite_etale :
    IsFinite (Objects.PELObject.auxiliaryLevelProjection A (L := L)).left ∧
      Etale (Objects.PELObject.auxiliaryLevelProjection A (L := L)).left :=
  Frame.Locus.LevelCover.fullFrameScheme_finite_etale A.polarized.abelian T.hom

/-- A single projective complex fiber suffices to make this finite
etale added-level family cover a connected prescribed-level family. -/
theorem Objects.PELObject.auxiliaryLevelProjection_surjective [PreconnectedSpace T.left]
    (q : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ T.left)
    (Q : Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.polarized.abelian.pullback q).scheme.left
      (A.polarized.abelian.pullback q).scheme.hom) :
    Surjective (Objects.PELObject.auxiliaryLevelProjection A (L := L)).left :=
  Level.CoverIs.LevelCover.fullFrame_surjective_of_complex_fiber A.polarized.abelian T.hom q Q

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL

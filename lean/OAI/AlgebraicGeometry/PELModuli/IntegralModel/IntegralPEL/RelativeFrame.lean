import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.Reconstruction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.RelativePullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.LevelReplacement

/-! # Relative Frame -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.RelativeFrame

noncomputable section

/-! Relative frame comparison before specializing to the representing
frame scheme, so its equations use only the actual family pullbacks. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X T : Over (Spec (.of R))}

def integralRelativeFrame (U : PEL.Has.IntegralPELObject P R iotaO N X) (Z : Over X.left)
    (β : (U.data.polarized.abelian.pullback Z.hom).FullLevel L) :
    IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N ((Over.map X.hom).obj Z) :=
  IntegralAdded.PELId.IntegralAddedPELLevel.ofPrescribed (U.pullback (Over.homMk Z.hom rfl)) β

def integralRelativeFrameIso (U : PEL.Has.IntegralPELObject P R iotaO N X) (Z : Over X.left)
    (β : (U.data.polarized.abelian.pullback Z.hom).FullLevel L)
    (f : T ⟶ X) (q : Over.mk f.left ⟶ Z) :
    IntegralAdded.PELId.IntegralAddedPELLevel.Iso
      ((integralRelativeFrame U Z β).pullback
        (Over.homMk q.left (by
          exact (Category.assoc _ _ _).symm.trans
            ((congrArg (fun z => z ≫ X.hom) q.w).trans f.w))))
      (IntegralAdded.PELId.IntegralAddedPELLevel.ofPrescribed (U.pullback f) (β.restrict q)) := by
  let e := PEL.Iso.PolarizedActionIso.relativePullback U.data q
  let c := AbelianModuli.ReferenceFamily.Pure.RelativeLevelIso.pureRelativePullbackIso U.data.polarized q
  have hc : e.polarized = c := PEL.Iso.PolarizedActionIso.relativePullback_polarized U.data q
  have hlevel : @AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.transport (3 * s) L T.left
      ((U.data.polarized.abelian.pullback Z.hom).pullback q.left)
      (U.data.polarized.abelian.pullback f.left)
      (β.pullback q.left) e.polarized.abelian e.polarized.abelianGroup = β.restrict q := by
    rw [hc]
    exact AbelianModuli.ReferenceFamily.Pure.RelativeLevelIso.pureRelativePullbackIso_level U.data.polarized q β
  let a := e.withLevel (β.pullback q.left) (β.restrict q) hlevel
  exact {
    auxiliary := a
    prescribed := by
      apply AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
      intro V c
      change (((U.data.polarized.level.pullback Z.hom).pullback q.left).hom.app (.op V) c).val ≫
        a.polarized.abelian.hom = _
      exact e.polarized.level V c }

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.RelativeFrame

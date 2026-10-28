import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.Transport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.FamilyBaseChange

/-! # Pullback Recovery Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An actual inverse-image ideal family is canonically isomorphic to the categorical pullback, compatibly with both its base map and its closed embedding. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem ClosedFamily.PullbackRecoveryIso.closedFamilyTransport_embedding {P Q : Scheme.{u}} (I : P.IdealSheafData) (p : Q ⟶ P) :
    ((I.comapIso p).hom ≫ pullback.snd p I.subschemeι) ≫ I.subschemeι =
      (I.comap p).subschemeι ≫ p := by
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, I.comapIso_hom_fst]

variable {S T : Scheme.{u}} {P : Over S} {Q : Over T}
variable (F : Closed.Families.FlatClosedFamily P) (p : Q.left ⟶ P.left) (f : T ⟶ S) (hp : IsPullback p Q.hom P.hom f)

def ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso : Q ≅ (Over.pullback f).obj P :=
  Over.isoMk hp.isoPullback hp.isoPullback_hom_snd

def Closed.Families.FlatClosedFamily.pullbackAlongIso :
    (F.pullbackAlong p f hp).scheme ≅ (Over.pullback f).obj F.scheme :=
  Over.isoMk (ClosedFamily.Transport.closedFamilyTransport_isPullback p f hp F.ideal).isoPullback
    (ClosedFamily.Transport.closedFamilyTransport_isPullback p f hp F.ideal).isoPullback_hom_snd

theorem Closed.Families.FlatClosedFamily.pullbackAlongIso_hom_fst :
    (F.pullbackAlongIso p f hp).hom.left ≫ pullback.fst F.scheme.hom f =
      (F.ideal.comapIso p).hom ≫ pullback.snd p F.ideal.subschemeι :=
  (ClosedFamily.Transport.closedFamilyTransport_isPullback p f hp F.ideal).isoPullback_hom_fst

theorem Closed.Families.FlatClosedFamily.pullbackAlongIso_inclusion :
    (F.pullbackAlongIso p f hp).hom ≫ (Over.pullback f).map F.inclusion =
      (F.pullbackAlong p f hp).inclusion ≫ (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso p f hp).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hi : ((Over.pullback f).map F.inclusion).left ≫ pullback.fst P.hom f =
        pullback.fst F.scheme.hom f ≫ F.inclusion.left := pullback.lift_fst _ _ _
    change ((F.pullbackAlongIso p f hp).hom.left ≫ ((Over.pullback f).map F.inclusion).left) ≫
        pullback.fst P.hom f =
      ((F.pullbackAlong p f hp).inclusion.left ≫ hp.isoPullback.hom) ≫ pullback.fst P.hom f
    rw [Category.assoc, hi, ← Category.assoc, F.pullbackAlongIso_hom_fst,
      Category.assoc, hp.isoPullback_hom_fst]
    exact ClosedFamily.PullbackRecoveryIso.closedFamilyTransport_embedding F.ideal p
  · exact ((F.pullbackAlongIso p f hp).hom ≫ (Over.pullback f).map F.inclusion).w.trans
      (((F.pullbackAlong p f hp).inclusion ≫ (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso p f hp).hom).w.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

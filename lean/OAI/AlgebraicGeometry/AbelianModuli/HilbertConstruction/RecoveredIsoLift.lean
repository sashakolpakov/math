import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveryFromPullbackIso

/-! # Recovered Iso Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveredIsoLift

noncomputable section

/-! Cartesian recovery lifts through any morphism whose actual base change is an isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} (r : T ⟶ S) {A : Over T} {X Y : Over S}
variable (i : Y ⟶ X) [IsIso ((Over.pullback r).map i)]
variable (q : A.left ⟶ X.left) (h : IsPullback q A.hom X.hom r)

def recoveredIsoLiftIso : A ≅ (Over.pullback r).obj Y :=
  Over.isoMk h.isoPullback h.isoPullback_hom_snd ≪≫ (asIso ((Over.pullback r).map i)).symm

def recoveredIsoLift : A.left ⟶ Y.left :=
  (recoveredIsoLiftIso r i q h).hom.left ≫ pullback.fst Y.hom r

theorem recoveredIsoLift_isPullback : IsPullback (recoveredIsoLift r i q h) A.hom Y.hom r :=
  RecoveryFromPullbackIso.schemeRecovery_isPullback_of_overIso r (recoveredIsoLiftIso r i q h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveredIsoLift

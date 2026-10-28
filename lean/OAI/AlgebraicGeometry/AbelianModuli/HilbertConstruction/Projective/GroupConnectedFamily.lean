import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ConnectedOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Group Connected Family -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GroupConnectedFamily

noncomputable section

/-! Restricting a smooth projective commutative group to its constructed connected-fiber open gives an actual abelian scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : Over S} [Smooth X.hom] [GrpObj X]
variable (P : ProjectivePresentations.ProjectivePresentation X)

def projectiveGroupConnectedOpen : S.Opens :=
  ConnectedOpen.pointedProjectiveConnectedOpen P η[X].left η[X].w

theorem projectiveGroupConnectedOpen_classifies {T : Scheme.{u}} (c : T ⟶ S) :
    GeometricallyConnected (pullback.snd X.hom c) ↔
      Set.range c ⊆ (projectiveGroupConnectedOpen P : Set S) :=
  ConnectedOpen.pointedProjectiveConnectedOpen_classifies P η[X].left η[X].w c

def projectiveGroupConnectedFamily : Over (projectiveGroupConnectedOpen P).toScheme :=
  (Over.pullback (projectiveGroupConnectedOpen P).ι).obj X

def projectiveGroupConnectedPresentation : ProjectivePresentations.ProjectivePresentation (projectiveGroupConnectedFamily P) :=
  P.baseChange (projectiveGroupConnectedOpen P).ι

instance projectiveGroupConnectedFamily_connected : GeometricallyConnected (projectiveGroupConnectedFamily P).hom :=
  ConnectedOpen.pointedProjectiveConnectedOpen_connected P η[X].left η[X].w

def projectiveGroupConnectedAbelianScheme (g : ℕ) [SmoothOfRelativeDimension g X.hom]
    [IsCommMonObj X] : Abelian.Schemes.AbelianScheme g (projectiveGroupConnectedOpen P).toScheme where
  scheme := projectiveGroupConnectedFamily P
  group := Functor.grpObjObj
  commutative := by
    let : GrpObj ((Over.pullback (projectiveGroupConnectedOpen P).ι).obj X) := Functor.grpObjObj
    exact inferInstanceAs (IsCommMonObj ((Over.pullback (projectiveGroupConnectedOpen P).ι).obj X))
  proper := (projectiveGroupConnectedPresentation P).proper
  smoothDimension := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
    (IsPullback.of_hasPullback X.hom (projectiveGroupConnectedOpen P).ι) inferInstance
  connected := projectiveGroupConnectedFamily_connected P

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GroupConnectedFamily

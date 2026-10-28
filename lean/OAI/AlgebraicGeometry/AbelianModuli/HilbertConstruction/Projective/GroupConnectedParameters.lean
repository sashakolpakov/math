import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GroupConnectedFamily
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveParameterCuts

/-! # Group Connected Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GroupConnectedParameters

noncomputable section

/-! The connected members of a projective smooth group family form an actual open parameter scheme with a universal abelian family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left]
variable (X : Over M.left) [Smooth X.hom] [GrpObj X] (P : ProjectivePresentations.ProjectivePresentation X)

def projectiveGroupConnectedParameter : Over S :=
  Open.ParameterPoints.openParameterScheme M (GroupConnectedFamily.projectiveGroupConnectedOpen P)

def projectiveGroupConnectedParameterInclusion : projectiveGroupConnectedParameter M X P ⟶ M :=
  Open.ParameterPoints.openParameterInclusion M (GroupConnectedFamily.projectiveGroupConnectedOpen P)

instance projectiveGroupConnectedParameterInclusion_open :
    IsOpenImmersion (projectiveGroupConnectedParameterInclusion M X P).left :=
  Open.ParameterPoints.openParameterInclusion_open M (GroupConnectedFamily.projectiveGroupConnectedOpen P)

def projectiveGroupConnectedParameterPointEquiv (T : Over S) :
    (T ⟶ projectiveGroupConnectedParameter M X P) ≃
      {c : T ⟶ M // GeometricallyConnected ((Over.pullback c.left).obj X).hom} :=
  (Open.ParameterPoints.openParameterPointEquiv M (GroupConnectedFamily.projectiveGroupConnectedOpen P) T).trans
    { toFun := fun c => ⟨c.val, (GroupConnectedFamily.projectiveGroupConnectedOpen_classifies P c.val.left).mpr c.property⟩
      invFun := fun c => ⟨c.val, (GroupConnectedFamily.projectiveGroupConnectedOpen_classifies P c.val.left).mp c.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

def projectiveGroupConnectedParameterQuasiProjectivePresentation [IsNoetherian S]
    (Q : ProjectivePresentations.QuasiProjectivePresentation M) : ProjectivePresentations.QuasiProjectivePresentation (projectiveGroupConnectedParameter M X P) :=
  Q.openParameter (GroupConnectedFamily.projectiveGroupConnectedOpen P)

def projectiveGroupConnectedUniversalAbelianScheme (g : ℕ)
    [SmoothOfRelativeDimension g X.hom] [IsCommMonObj X] :
    Abelian.Schemes.AbelianScheme g (projectiveGroupConnectedParameter M X P).left :=
  GroupConnectedFamily.projectiveGroupConnectedAbelianScheme P g

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GroupConnectedParameters

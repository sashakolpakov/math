import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GroupConnectedParameters

/-! # Group Connected Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GroupConnectedRepresentation

noncomputable section

/-! The constructed connected-group open represents the geometric connectedness subfunctor on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left]
variable (X : Over M.left) [Smooth X.hom] [GrpObj X] (P : ProjectivePresentations.ProjectivePresentation X)

def projectiveGroupConnectedSubfunctor : Subfunctor (yoneda.obj M) where
  obj _ := {c | GeometricallyConnected ((Over.pullback c.left).obj X).hom}
  map f c hc := by
    apply (GroupConnectedFamily.projectiveGroupConnectedOpen_classifies P (f.unop ≫ c).left).mpr
    have h := (GroupConnectedFamily.projectiveGroupConnectedOpen_classifies P c.left).mp hc
    rintro s ⟨t, rfl⟩
    exact h ⟨f.unop.left t, rfl⟩

def projectiveGroupConnectedClassifyingIso :
    yoneda.obj (GroupConnectedParameters.projectiveGroupConnectedParameter M X P) ≅
      (projectiveGroupConnectedSubfunctor M X P).toFunctor :=
  NatIso.ofComponents (fun T => (GroupConnectedParameters.projectiveGroupConnectedParameterPointEquiv M X P T.unop).toIso) (by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro y
    apply Subtype.ext
    change (f.unop ≫ y) ≫ GroupConnectedParameters.projectiveGroupConnectedParameterInclusion M X P =
      f.unop ≫ (y ≫ GroupConnectedParameters.projectiveGroupConnectedParameterInclusion M X P)
    exact Category.assoc _ _ _)

theorem projectiveGroupConnected_quasiProjective_representation [IsNoetherian S]
    (Q : ProjectivePresentations.QuasiProjectivePresentation M) :
    ∃ Z : Over S, Nonempty (ProjectivePresentations.QuasiProjectivePresentation Z) ∧
      Nonempty ((projectiveGroupConnectedSubfunctor M X P).toFunctor ≅ yoneda.obj Z) :=
  ⟨GroupConnectedParameters.projectiveGroupConnectedParameter M X P,
    ⟨GroupConnectedParameters.projectiveGroupConnectedParameterQuasiProjectivePresentation M X P Q⟩,
    ⟨(projectiveGroupConnectedClassifyingIso M X P).symm⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GroupConnectedRepresentation

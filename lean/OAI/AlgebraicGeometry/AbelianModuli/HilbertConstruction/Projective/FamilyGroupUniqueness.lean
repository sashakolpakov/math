import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.MonoidUniqueness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyOperationData

/-! # Family Group Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! On a projectively presented smooth family with geometrically connected
fibers, the unit determines the commutative group operations over a locally
Noetherian base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem FamilyGroup.Operations.FamilyGroupOperations.eq_of_unit_eq_projective
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g : ℕ} {X : Over S}
    [SmoothOfRelativeDimension g X.hom] [GeometricallyConnected X.hom]
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) (D E : FamilyGroup.Operations.FamilyGroupOperations X)
    (hD : D.Laws) (hE : E.Laws) (hu : D.unit = E.unit) : D = E := by
  let A : Abelian.Schemes.AbelianScheme g S :=
    { scheme := X
      group := D.groupObj hD
      commutative := D.groupObj_comm hD
      proper := P.proper
      smoothDimension := inferInstance
      connected := inferInstance }
  have hm : E.mul = D.mul :=
    Projective.MonoidUniqueness.projectiveAbelian_monoid_multiplication_unique A P (E.groupObj hE).toMonObj hu.symm
  have hg : D.groupObj hD = E.groupObj hE :=
    GrpObj.ext _ _ (MonObj.ext _ _ hm.symm)
  exact FamilyGroup.Operations.FamilyGroupOperations.ext D E hu hm.symm
    (congrArg (fun G : GrpObj X => G.inv) hg)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

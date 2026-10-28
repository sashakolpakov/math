import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectivePresentation
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCohomology
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections

/-! # Section Finiteness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.SectionFiniteness

noncomputable section

/-! Finite global sections for any coherent module on a scheme with
an actual projective presentation over a noetherian affine base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections
universe u

theorem projectivePresentation_globalSections_finite
    {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (X : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X)
    (M : X.left.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite Γ(S, ⊤) ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor X.hom).obj M) := by
  let p := Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.base X P
  let U := Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover X P
  have hU : TopologicalSpace.IsOpenCover U :=
    TopologicalSpace.IsOpenCover.mk (Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.covers X P)
  have : Module.Finite Γ(Spec (.of Γ(S, ⊤)), ⊤)
      ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex p M U).homology 0) :=
    Quotients.FiniteDescent.ProjectiveCohomology.Construction.ProjectiveCechComplex.finite X P M 0
  have ht : Module.Finite Γ(Spec (.of Γ(S, ⊤)), ⊤) ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor p).obj M) :=
    Module.Finite.equiv (SheafCohomology.Projective.BaseZeroSections.orderedBaseCechHZeroGlobalSectionsLinearEquiv p M U hU)
  have hp : p = X.hom ≫ S.toSpecΓ := Quotients.FiniteDescent.ProjectivePresentation.Construction.ProjectivePresentationEmbedding.map_base X P
  rw [hp] at ht
  let := ht
  let e : (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (X.hom ≫ S.toSpecΓ)).obj M →ₛₗ[S.toSpecΓ.appTop.hom]
      (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor X.hom).obj M :=
    { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_surjective e Function.surjective_id

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.SectionFiniteness

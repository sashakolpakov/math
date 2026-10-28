import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectivePerfectCech
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechScalarCoface
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RestrictedHomology

/-! # Projective Base Ring Model -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveBaseRingModel

noncomputable section

/-! The finite projective model over the global functions of the original base. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.ProjectiveCechComplex

variable {S : Scheme.{u}} (X : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X)

def actualComplex (M : X.left.Modules) : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ :=
  SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex X.hom M (ProjectiveCechAt.Construction.ProjectiveCechComplex.cover X P)

def actualRestrictionIso (M : X.left.Modules) : ProjectiveCechAt.Construction.ProjectiveCechComplex.complex X P M ≅
    ((ModuleCat.restrictScalars S.toSpecΓ.appTop.hom).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (actualComplex X P M) := by
  have hb : ProjectiveCechAt.Construction.ProjectiveCechComplex.base X P = X.hom ≫ S.toSpecΓ := ProjectivePresentation.Construction.ProjectivePresentationEmbedding.map_base X P
  exact eqToIso (congrArg (fun f => SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f M (ProjectiveCechAt.Construction.ProjectiveCechComplex.cover X P)) hb) ≪≫
    CechScalarCoface.Construction.CechScalarRestriction.complexIso X.hom S.toSpecΓ M (ProjectiveCechAt.Construction.ProjectiveCechComplex.cover X P)

variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]

theorem actual_finite (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (q : ℕ) :
    Module.Finite Γ(S, ⊤) ((actualComplex X P L.sheaf).homology q) := by
  have := ProjectiveCohomology.Construction.ProjectiveCechComplex.lineBundle_finite X P L q
  exact RestrictedHomology.Construction.RestrictedHomologyFinite.finite S.toSpecΓ.appTop.hom
    (actualComplex X P L.sheaf) (actualRestrictionIso X P L.sheaf) q

theorem exists_actual_finite_projective [Flat X.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) :
    ∃ (D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ)
      (φ : D ⟶ actualComplex X P L.sheaf),
      QuasiIso φ ∧
      (∃ N, ∀ q, N ≤ q → IsZero (D.X q)) ∧
      (∀ q, Module.Finite Γ(S, ⊤) (D.X q)) ∧
      (∀ q, Module.Projective Γ(S, ⊤) (D.X q)) ∧
      (∀ (A : Type u) [AddCommGroup A] [Module Γ(S, ⊤) A],
        QuasiIso (ModuleTensor.Construction.ModuleTensorFunctor.map A φ)) := by
  apply BoundedProjectiveComplex.Construction.CochainFiniteModel.exists_finite_projective_complex (actualComplex X P L.sheaf)
  · refine ⟨P.dimension + 1, fun q hq => ?_⟩
    apply SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechObject_isZero_of_card_le
    simpa only [Fintype.card_ulift, Fintype.card_fin] using hq
  · exact fun q => OrderedCechObject.Construction.OrderedCechFlat.complex X.hom L.sheaf
      (LineBundleFree.Construction.LineBundleCoherence.invertible L) (ProjectiveCechAt.Construction.ProjectiveCechComplex.cover X P) (ProjectiveCechFlat.Construction.ProjectiveCechComplex.intersection_affine X P) q
  · exact actual_finite X P L

end Construction.ProjectiveCechComplex

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveBaseRingModel

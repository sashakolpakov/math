import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCechFlat
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCohomology
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BoundedProjectiveComplex

/-! # Projective Perfect Cech -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectivePerfectCech.Construction.ProjectiveCechComplex

noncomputable section

/-! A bounded finite projective model of line-bundle Cech cohomology over
any Noetherian affine base, with universal tensor comparison. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable (X : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) [Flat X.hom]

theorem exists_finite_projective (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) :
    ∃ (D : CochainComplex (ModuleCat.{u} Γ(Spec (.of Γ(S, ⊤)), ⊤)) ℕ)
      (φ : D ⟶ ProjectiveCechAt.Construction.ProjectiveCechComplex.complex X P L.sheaf),
      QuasiIso φ ∧
      (∃ N, ∀ q, N ≤ q → IsZero (D.X q)) ∧
      (∀ q, Module.Finite Γ(Spec (.of Γ(S, ⊤)), ⊤) (D.X q)) ∧
      (∀ q, Module.Projective Γ(Spec (.of Γ(S, ⊤)), ⊤) (D.X q)) ∧
      (∀ (A : Type u) [AddCommGroup A] [Module Γ(Spec (.of Γ(S, ⊤)), ⊤) A],
        QuasiIso (ModuleTensor.Construction.ModuleTensorFunctor.map A φ)) := by
  let e : Γ(Spec (.of Γ(S, ⊤)), ⊤) ≃+* Γ(S, ⊤) :=
    (Scheme.ΓSpecIso (.of Γ(S, ⊤))).commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ(Spec (.of Γ(S, ⊤)), ⊤) :=
    isNoetherianRing_of_ringEquiv Γ(S, ⊤) e.symm
  exact BoundedProjectiveComplex.Construction.CochainFiniteModel.exists_finite_projective_complex (ProjectiveCechAt.Construction.ProjectiveCechComplex.complex X P L.sheaf)
    ⟨P.dimension + 1, ProjectiveCechAt.Construction.ProjectiveCechComplex.bounded X P L.sheaf⟩
    (ProjectiveCechFlat.Construction.ProjectiveCechComplex.lineBundle_flat X P L) (ProjectiveCohomology.Construction.ProjectiveCechComplex.lineBundle_finite X P L)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectivePerfectCech.Construction.ProjectiveCechComplex

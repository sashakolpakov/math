import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations
import OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure

/-! # Projective Presentation -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectivePresentation.Construction.ProjectivePresentationEmbedding

noncomputable section

/-! An affine-base projective presentation as a closed immersion into
the polynomial Proj used by the cohomology complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations

universe u

theorem base_eq (R : Type u) [CommRing R] (n : ℕ) :
    (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).hom =
      SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1)) := by
  unfold AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ
  congr 2

variable {S : Scheme.{u}} (X : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X)

def map : X.left ⟶ Proj (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) P.dimension) :=
  P.embedding.left ≫ pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) P.dimension).hom S.toSpecΓ

theorem map_base : map X P ≫
    SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := Γ(S, ⊤)) (σ := Fin (P.dimension + 1)) =
      X.hom ≫ S.toSpecΓ := by
  rw [← base_eq]
  let e : X.left ⟶ pullback (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) P.dimension).hom S.toSpecΓ :=
    P.embedding.left
  change e ≫ pullback.fst _ _ ≫ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) P.dimension).hom = _
  rw [pullback.condition, ← Category.assoc]
  exact congrArg (fun a => a ≫ S.toSpecΓ) (Over.w P.embedding)

theorem closed [IsAffine S] : IsClosedImmersion (map X P) := by
  let e : X.left ⟶ pullback (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) P.dimension).hom S.toSpecΓ :=
    P.embedding.left
  have : IsClosedImmersion e := P.closedImmersion
  have : IsIso (pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) P.dimension).hom S.toSpecΓ) :=
    inferInstance
  change IsClosedImmersion (e ≫ pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) P.dimension).hom S.toSpecΓ)
  infer_instance

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectivePresentation.Construction.ProjectivePresentationEmbedding

import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectivePresentation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Projective Cech At -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex

noncomputable section

/-! The bounded affine Cech complex attached to an actual projective presentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

variable {S : Scheme.{u}} (X : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X)

def base : X.left ⟶ Spec (.of Γ(S, ⊤)) :=
  ProjectivePresentation.Construction.ProjectivePresentationEmbedding.map X P ≫
    SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := Γ(S, ⊤)) (σ := Fin (P.dimension + 1))

def cover (i : ULift.{u} (Fin (P.dimension + 1))) : X.left.Opens :=
  ProjectivePresentation.Construction.ProjectivePresentationEmbedding.map X P ⁻¹ᵁ SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover i

theorem covers : iSup (cover X P) = ⊤ := by
  apply top_unique
  intro x _
  have hx : ProjectivePresentation.Construction.ProjectivePresentationEmbedding.map X P x ∈
      iSup (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := Γ(S, ⊤)) :
        ULift.{u} (Fin (P.dimension + 1)) → (Proj _).Opens) := by
    rw [SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩

theorem affine [IsAffine S] (i : ULift.{u} (Fin (P.dimension + 1))) :
    IsAffineOpen (cover X P i) := by
  have := ProjectivePresentation.Construction.ProjectivePresentationEmbedding.closed X P
  exact (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen i).preimage
    (ProjectivePresentation.Construction.ProjectivePresentationEmbedding.map X P)

def complex (M : X.left.Modules) :
    CochainComplex (ModuleCat Γ(Spec (.of Γ(S, ⊤)), ⊤)) ℕ :=
  SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex (base X P) M (cover X P)

theorem bounded (M : X.left.Modules) (q : ℕ) (hq : P.dimension + 1 ≤ q) :
    IsZero ((complex X P M).X q) := by
  apply SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechObject_isZero_of_card_le
  simpa only [Fintype.card_ulift, Fintype.card_fin] using hq

theorem exactAt (M : X.left.Modules) (q : ℕ) (hq : P.dimension + 1 ≤ q) :
    (complex X P M).ExactAt q := by
  apply SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex_exactAt_of_card_le
  simpa only [Fintype.card_ulift, Fintype.card_fin] using hq

theorem base_flat [IsAffine S] [Flat X.hom] : Flat (base X P) := by
  change Flat (ProjectivePresentation.Construction.ProjectivePresentationEmbedding.map X P ≫ _)
  rw [ProjectivePresentation.Construction.ProjectivePresentationEmbedding.map_base]
  infer_instance

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex

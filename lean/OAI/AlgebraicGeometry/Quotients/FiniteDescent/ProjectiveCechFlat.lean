import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCechAt
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechObject
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree

/-! # Projective Cech Flat -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCechFlat.Construction.ProjectiveCechComplex

noncomputable section

/-! The projective Cech model of an invertible sheaf is termwise flat over a flat base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

variable {S : Scheme.{u}} [IsAffine S]
variable (X : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X)

theorem intersection_affine (q : ℕ) (i : Fin (q + 1) → ULift.{u} (Fin (P.dimension + 1))) :
    IsAffineOpen (∏ᶜ fun k : Fin (q + 1) => ProjectiveCechAt.Construction.ProjectiveCechComplex.cover X P (i k)) := by
  have := ProjectivePresentation.Construction.ProjectivePresentationEmbedding.closed X P
  change IsAffineOpen (∏ᶜ fun k : Fin (q + 1) =>
    ProjectivePresentation.Construction.ProjectivePresentationEmbedding.map X P ⁻¹ᵁ SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (i k))
  rw [← SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection]
  exact (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_isAffineOpen i).preimage
    (ProjectivePresentation.Construction.ProjectivePresentationEmbedding.map X P)

theorem flat [Flat X.hom] (M : X.left.Modules) (hM : SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible M) (q : ℕ) :
    Module.Flat Γ(Spec (.of Γ(S, ⊤)), ⊤) ((ProjectiveCechAt.Construction.ProjectiveCechComplex.complex X P M).X q) := by
  have := ProjectiveCechAt.Construction.ProjectiveCechComplex.base_flat X P
  exact OrderedCechObject.Construction.OrderedCechFlat.complex (ProjectiveCechAt.Construction.ProjectiveCechComplex.base X P) M hM (ProjectiveCechAt.Construction.ProjectiveCechComplex.cover X P) (intersection_affine X P) q

theorem lineBundle_flat [Flat X.hom] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (q : ℕ) :
    Module.Flat Γ(Spec (.of Γ(S, ⊤)), ⊤) ((ProjectiveCechAt.Construction.ProjectiveCechComplex.complex X P L.sheaf).X q) :=
  flat X P L.sheaf (LineBundleFree.Construction.LineBundleCoherence.invertible L) q

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCechFlat.Construction.ProjectiveCechComplex

import OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeAbelianDimension
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter

/-! # Abelian Model Dimension -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianModelDimension

noncomputable section

/-! A specified complex abelian model fixes the relative dimension
of its smooth proper connected arithmetic model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem complex_abelian_total_dimension {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) :
    topologicalKrullDim A.scheme.left = (g : WithBot ℕ∞) := by
  let : IsIntegral A.scheme.left := AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A
  rw [IntegralModel.Group.FamilyDimension.group_krullDim_eq_transcendenceDimension A.scheme,
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension,
    AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.dimension_eq]

def abelianSchemeOfComplexModel
    {S : Scheme.{0}} [ConnectedSpace S] (X : Over S) [GrpObj X] [IsCommMonObj X]
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (e : (Over.pullback c).obj X ≅ A.scheme) : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S := by
  have : IsIso e.hom.left := ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e).isIso_hom
  have hdim : topologicalKrullDim ((Over.pullback c).obj X).left = (g : WithBot ℕ∞) :=
    e.hom.left.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
      (complex_abelian_total_dimension A)
  exact RelativeAbelianDimension.abelianSchemeOfOneFiber X c g hdim

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianModelDimension

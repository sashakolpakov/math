import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.GroupModel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.Dimension
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.PolarizedProjectivity

/-! # Abelian Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric

noncomputable section

/-! The spread group family has the original relative dimension and
therefore gives an actual HilbertConstruction abelian scheme over its coefficient base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {g n : ℕ}
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (D : GroupModel.GeometricGroupModel A.scheme n)

section

theorem GroupModel.GeometricGroupModel.smoothDimension : SmoothOfRelativeDimension g D.data.toModel.model.hom := by
  let M := D.data.toModel.model
  let p := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ k D.data.toModel.coefficients
  have : IsSchemeTheoreticallyDominant p := ArithmeticGeometry.Models.SpreadingOut.GenericFaithfulness.Construction.spec_injective_schematically_dominant
    (algebraMap (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing ℚ k D.data.toModel.coefficients) k) Subtype.val_injective
  have : IsDominant p := inferInstance
  have : IsIso D.data.toModel.genericIso.hom.left :=
    ((Over.forget (Spec (.of k))).mapIso D.data.toModel.genericIso).isIso_hom
  have hdim : topologicalKrullDim ((Over.pullback p).obj M).left = (g : WithBot ℕ∞) :=
    D.data.toModel.genericIso.hom.left.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
      (Dimension.geometricAbelian_krullDim A)
  exact ArithmeticGeometry.Descent.CMVariety.GroupFamilyDimension.Abelian.smooth_group_dimension_of_dominant_fiber M p g hdim

def GroupModel.GeometricGroupModel.abelian : HilbertConstruction.Abelian.Schemes.AbelianScheme g (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase ℚ k D.data.toModel.coefficients) where
  scheme := D.data.toModel.model
  group := D.group
  commutative := D.commutative
  proper := D.proper
  smoothDimension := GroupModel.GeometricGroupModel.smoothDimension A D
  connected := D.connected

def GroupModel.GeometricGroupModel.fiberIso : ((GroupModel.GeometricGroupModel.abelian A D).pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ k D.data.toModel.coefficients)).scheme ≅
    A.scheme := D.data.toModel.genericIso

instance GroupModel.GeometricGroupModel.fiberIso_isMonHom : IsMonHom (GroupModel.GeometricGroupModel.fiberIso A D).hom := D.comparison_group

end

theorem AbelianModel.geometricPolarized_has_abelian_model {N : ℕ} {δ : Fin g → ℕ}
    (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) :
    Nonempty (GroupModel.GeometricGroupModel B.abelian.scheme (PolarizedProjectivity.geometricPolarizedProjectivePresentation B).dimension) := by
  let : IsIntegral B.abelian.scheme.left :=
    Picard.Homomorphisms.GroupRigidity.Construction.integral_smooth_proper_connected_group B.abelian.scheme
  exact GroupModel.exists_geometric_group_model B.abelian.scheme _ (PolarizedProjectivity.geometricPolarizedProjectiveEmbedding B)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric

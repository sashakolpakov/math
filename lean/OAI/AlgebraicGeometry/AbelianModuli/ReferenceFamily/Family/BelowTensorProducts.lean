import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenProductNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.AlgebraSquare

/-! # Below Tensor Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.BelowTensorProducts

noncomputable section

section

/-! The constructed common-open product charts commute with the
literal affine scheme restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R))) [Smooth X.hom]

attribute [local irreducible] CommonOpenProducts.familyCommonOpenProductEquiv
attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

theorem familyCommonOpenProduct_scheme_square {U V W : X.left.affineOpens}
    (t : U.1 ≤ V.1) (h : V.1 ≤ W.1) (d : Derivation k R k) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom (DualNumber k)
        (DualNumber k ⊗[k] (k ⊗[R] AffineTangentLifts.familyAffineRing R X V))
        (DualNumber k ⊗[k] (k ⊗[R] AffineTangentLifts.familyAffineRing R X U)) (ProductRestrictionMaps.familyProductTensorRestriction k R X t) ≫
      (EtaleSplittingAt.EtaleSplitting.affineAlgIso (DualNumber k) (DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X V)
        (CommonOpenProducts.familyCommonOpenProductEquiv k R X h d)).hom =
      (EtaleSplittingAt.EtaleSplitting.affineAlgIso (DualNumber k) (DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X U)
        (CommonOpenProducts.familyCommonOpenProductEquiv k R X (t.trans h) d)).hom ≫
        Affine.AlgebraAutomorphismNaturality.affineOverAlgHom (DualNumber k) (DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X V)
          (DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X U) (ProductRestrictionMaps.familyTangentTensorRestriction k R X t d) := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Affine.AlgebraAutomorphismNaturality.affineOverAlgHom_left, Affine.AlgebraSquare.affineAlgIso_hom_left]
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (AlgHom.congr_fun (CommonOpenProductNaturality.familyCommonOpenProductEquiv_restrict k R X t h d) a).symm

end

/-! On all affine subopens of one chart, the constructed products
form a natural isomorphism of the actual tensor-coordinate scheme
diagrams. Every component is the product from the restricted lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R))) [Smooth X.hom]

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver Affine.AlgebraAutomorphismNaturality.affineOverAlgHom
attribute [local irreducible] CommonOpenProducts.familyCommonOpenProductEquiv

def familyBelowTangentTensorIso (W : X.left.affineOpens) (d : Derivation k R k) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    Over.forget W ⋙ HilbertConstruction.AlgebraSchemeDiagrams.algebraSchemeDiagram (DualNumber k)
      (FixedFiber.AffineDiagram.fixedFiberTensorAlgebras R k X ⋙ HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor k (DualNumber k)) ≅
        Over.forget W ⋙ FixedFiber.AffineDiagram.fixedFiberTensorDiagram R (DualNumber k) X := by
  let qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
  let : Module R (DualNumber k) := qD.toModule
  let : SMul R (DualNumber k) := qD.toSMul
  refine NatIso.ofComponents (fun V => ?_) (fun {V V'} f => ?_)
  · exact EtaleSplittingAt.EtaleSplitting.affineAlgIso (DualNumber k) (DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X V.left)
      (CommonOpenProducts.familyCommonOpenProductEquiv k R X V.hom.le d)
  · exact familyCommonOpenProduct_scheme_square k R X f.left.le V'.hom.le d

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.BelowTensorProducts

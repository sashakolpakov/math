import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedProducts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.AlgebraSquare

/-! # Corrected Scheme Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedSchemeSquare

noncomputable section

section

/-! The corrected tensor products commute with the literal affine
scheme maps, with both sides over the actual dual-number base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R))) [Smooth X.hom]

attribute [local irreducible] CorrectedProducts.familyCorrectedProductEquiv
attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

theorem familyCorrectedProduct_scheme_square {U V W : X.left.affineOpens}
    (t : U.1 ≤ V.1) (h : V.1 ≤ W.1) (d : Derivation k R k)
    (a : Derivation k (k ⊗[R] AffineTangentLifts.familyAffineRing R X W) (k ⊗[R] AffineTangentLifts.familyAffineRing R X W)) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom (DualNumber k)
        (DualNumber k ⊗[k] (k ⊗[R] AffineTangentLifts.familyAffineRing R X V))
        (DualNumber k ⊗[k] (k ⊗[R] AffineTangentLifts.familyAffineRing R X U)) (ProductRestrictionMaps.familyProductTensorRestriction k R X t) ≫
      (EtaleSplittingAt.EtaleSplitting.affineAlgIso (DualNumber k) (DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X V)
        (CorrectedProducts.familyCorrectedProductEquiv k R X h d a)).hom =
      (EtaleSplittingAt.EtaleSplitting.affineAlgIso (DualNumber k) (DualNumber k ⊗[R] AffineTangentLifts.familyAffineRing R X U)
        (CorrectedProducts.familyCorrectedProductEquiv k R X (t.trans h) d a)).hom ≫
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
  intro b
  exact (AlgHom.congr_fun (CorrectedProducts.familyCorrectedProductEquiv_restrict k R X t h d a) b).symm

end

/-! Corrected product charts form a natural isomorphism on all
affine subopens of the chart carrying the correction derivation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R))) [Smooth X.hom]

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver Affine.AlgebraAutomorphismNaturality.affineOverAlgHom
attribute [local irreducible] CorrectedProducts.familyCorrectedProductEquiv

def familyBelowCorrectedTensorIso (W : X.left.affineOpens) (d : Derivation k R k)
    (a : Derivation k (k ⊗[R] AffineTangentLifts.familyAffineRing R X W) (k ⊗[R] AffineTangentLifts.familyAffineRing R X W)) :
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
      (CorrectedProducts.familyCorrectedProductEquiv k R X V.hom.le d a)
  · exact familyCorrectedProduct_scheme_square k R X f.left.le V'.hom.le d a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedSchemeSquare

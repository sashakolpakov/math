import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualPullbackMorphismRigidity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TransportedMultiplicationIdentity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointedNormalizedDualProduct

/-! # Product Group Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductGroupIso

noncomputable section

/-! A pointed normalized carrier isomorphism of a commutative group
family with proper smooth connected special fiber preserves multiplication.
Thus the actual normalized scheme product upgrades to a group product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (X : Over (Spec (.of (DualNumber ℂ)))) [GrpObj X] [IsCommMonObj X]
    [Smooth ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj X).hom]
    [IsProper ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj X).hom]
    [GeometricallyConnected ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj X).hom]
    (e : X ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj X))

theorem pointedNormalizedDualProduct_isMonHom (he : OpenProductData.NormalizesDualProductFiber ℂ e)
    (hp : η[X] ≫ e.hom = η[(Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj X)]) :
    IsMonHom e.hom := by
  refine ⟨hp, ?_⟩
  let F := Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)
  let G := Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)
  let A := G.obj X
  have : Smooth (A ⊗ A).hom := inferInstanceAs (Smooth (pullback.fst A.hom A.hom ≫ A.hom))
  have : IsProper (A ⊗ A).hom := inferInstanceAs (IsProper (pullback.fst A.hom A.hom ≫ A.hom))
  have : GeometricallyConnected (A ⊗ A).hom :=
    GeometricallyConnected.comp (pullback.fst A.hom A.hom) A.hom
  have h := DualPullbackMorphismRigidity.properDualPullbackMorphism_ext (A ⊗ A) A
    (TransportedMultiplicationIdentity.productMultiplicationTransport F G X e) (TransportedMultiplicationIdentity.productMultiplicationReference F G X)
    (TransportedMultiplicationIdentity.productMultiplicationTransport_reduction F G X e (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso ℂ) he)
    (TransportedMultiplicationIdentity.productMultiplicationTransport_identity F G X e hp)
  exact TransportedMultiplicationIdentity.productMultiplication_eq_of_transport F G X e h

theorem exists_normalized_groupDualProduct (he : OpenProductData.NormalizesDualProductFiber ℂ e) :
    ∃ e' : X ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj X),
      OpenProductData.NormalizesDualProductFiber ℂ e' ∧ IsMonHom e'.hom := by
  obtain ⟨e', he', hp⟩ := PointedNormalizedDualProduct.exists_pointed_normalizedDualProduct ℂ X e he
  exact ⟨e', he', pointedNormalizedDualProduct_isMonHom X e' he' hp⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductGroupIso

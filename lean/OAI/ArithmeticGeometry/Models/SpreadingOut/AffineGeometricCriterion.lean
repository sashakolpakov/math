import OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricFieldComponents

/-! # Affine Geometric Criterion -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.AffineGeometricCriterion.Construction

noncomputable section

/-! Field-valued tensor-domain criteria for geometric irreducibility and
connectedness of an affine morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

theorem affine_geometricallyIrreducible_of_tensor_domains
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (h : ∀ (K : Type u) [Field K] [Algebra R K], IsDomain (K ⊗[R] A)) :
    GeometricallyIrreducible (Affine.Construction.affineOver R A).hom := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr fun K _ _ ↦ ?_⟩
  have := h K
  let e : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
      (Affine.Construction.affineOver R A)).left ≅ Spec (.of (K ⊗[R] A)) :=
    (Over.forget (Spec (.of K))).mapIso (Affine.Construction.baseChangeAffineIso R K A)
  have : IsIntegral (Spec (.of (K ⊗[R] A))) := inferInstance
  have : IsIntegral ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
      (Affine.Construction.affineOver R A)).left := IsIntegral.of_isIso e.inv
  exact inferInstanceAs (IrreducibleSpace ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj (Affine.Construction.affineOver R A)).left)

theorem affine_geometricallyConnected_of_tensor_domains
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (h : ∀ (K : Type u) [Field K] [Algebra R K], IsDomain (K ⊗[R] A)) :
    GeometricallyConnected (Affine.Construction.affineOver R A).hom := by
  have hgeom : GeometricallyIrreducible (Affine.Construction.affineOver R A).hom :=
    affine_geometricallyIrreducible_of_tensor_domains R A h
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ g ↦ ?_⟩
  have : IrreducibleSpace (pullback (Affine.Construction.affineOver R A).hom g : Scheme.{u}) :=
    pullback_of_geometrically hgeom.geometrically_irreducibleSpace K g
  infer_instance

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.AffineGeometricCriterion.Construction

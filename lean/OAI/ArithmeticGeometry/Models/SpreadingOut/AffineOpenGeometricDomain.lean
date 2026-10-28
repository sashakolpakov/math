import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality
import OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricPrincipal

/-! # Affine Open Geometric Domain -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.AffineOpenGeometricDomain.Construction

noncomputable section

/-! The coordinate algebra of an affine open in a smooth geometrically
irreducible scheme remains a domain after every field extension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

theorem affine_open_tensor_domain
    (K L A : Type u) [Field K] [Field L] [Algebra K L]
    [CommRing A] [IsDomain A] [Algebra K A]
    (X : Over (Spec (.of K))) [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (j : Affine.Construction.affineOver K A ⟶ X) [IsOpenImmersion j.left] : IsDomain (L ⊗[K] A) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let F := Over.pullback g
  have : IrreducibleSpace (F.obj X).left :=
    pullback_of_geometrically GeometricallyIrreducible.geometrically_irreducibleSpace L g
  have : IsReduced (F.obj X).left := SmoothComponents.Construction.smooth_scheme_reduced (pullback.snd X.hom g)
  have : IsIntegral (F.obj X).left := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsOpenImmersion (F.map j).left := MorphismProperty.of_isPullback
    (FoundationsPullback.Constructions.pullback_over_map_isPullback g j).flip inferInstance
  have hn : Nonempty (F.obj (Affine.Construction.affineOver K A)).left := by
    let x : (Affine.Construction.affineOver K A).left := Classical.choice (inferInstanceAs (Nonempty (Spec (.of A))))
    obtain ⟨y, -⟩ := (pullback.fst (Affine.Construction.affineOver K A).hom g).surjective x
    exact ⟨y⟩
  have : IsIntegral (F.obj (Affine.Construction.affineOver K A)).left := isIntegral_of_isOpenImmersion (F.map j).left
  let e : (F.obj (Affine.Construction.affineOver K A)).left ≅ Spec (.of (L ⊗[K] A)) :=
    (Over.forget (Spec (.of L))).mapIso (Affine.Construction.baseChangeAffineIso K L A)
  have : IsIntegral (Spec (.of (L ⊗[K] A))) := IsIntegral.of_isIso e.hom
  exact (affine_isIntegral_iff _).mp this

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.AffineOpenGeometricDomain.Construction

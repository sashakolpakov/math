import OAI.RepresentationTheory.Theta.Geometric.Affine.BaseChangeCoordinates

/-! # Base Change Function Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.BaseChangeFunctionDescent

noncomputable section

/-! Coefficient descent on every native affine open of a flat base
change of an algebra equalizer. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {A R P : Type} [CommRing A] [CommRing R] [CommRing P]
    [Algebra A R] [Algebra A P]
    (hi : Function.Injective (algebraMap A R)) (f g : R →ₐ[A] P)
    (he : Function.Exact (Algebra.linearMap A R) (f.toLinearMap - g.toLinearMap))

include hi he in
theorem flat_pullback_fst_hasRegularFunctionDescent {X : Scheme} [IsAffine X]
    (h : X ⟶ Spec (.of A)) [Flat h] :
    RegularFunctionDescent.HasRegularFunctionDescent (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap A R)))) := by
  let : Algebra A Γ(X, ⊤) := Affine.StructureCoordinates.affineStructureAlgebra h
  let : Module.Flat A Γ(X, ⊤) := Affine.StructureCoordinates.affineStructure_flat h
  exact RegularFunctionDescent.HasRegularFunctionDescent.of_isomorphic
    (RegularFunctionDescent.flatEqualizerSpecMap_hasRegularFunctionDescent (T := Γ(X, ⊤)) hi f g he)
    (Affine.BaseChangeCoordinates.affineBaseChangeCoordinateIso (R := R) h).symm X.isoSpec.symm
    (Affine.BaseChangeCoordinates.affineBaseChangeCoordinateIso_inv_fst h)

include hi he in
theorem flat_isPullback_hasRegularFunctionDescent {X Z : Scheme} [IsAffine X]
    (h : X ⟶ Spec (.of A)) [Flat h] (u : Z ⟶ X) (v : Z ⟶ Spec (.of R))
    (H : IsPullback u v h (Spec.map (CommRingCat.ofHom (algebraMap A R)))) :
    RegularFunctionDescent.HasRegularFunctionDescent u := by
  apply RegularFunctionDescent.HasRegularFunctionDescent.of_isomorphic (flat_pullback_fst_hasRegularFunctionDescent hi f g he h)
    H.isoPullback.symm (Iso.refl X)
  simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id] using H.isoPullback_inv_fst

include hi he in
theorem flat_isPullback_affineFunctionDescent {Y Z : Scheme}
    (h : Y ⟶ Spec (.of A)) [Flat h] (u : Z ⟶ Y) (v : Z ⟶ Spec (.of R))
    (H : IsPullback u v h (Spec.map (CommRingCat.ofHom (algebraMap A R))))
    (U : Y.Opens) (hU : IsAffineOpen U) : RegularFunctionDescent.HasRegularFunctionDescent (u ∣_ U) := by
  have : IsAffine U.toScheme := hU
  exact flat_isPullback_hasRegularFunctionDescent hi f g he (U.ι ≫ h) (u ∣_ U)
    ((u ⁻¹ᵁ U).ι ≫ v) ((isPullback_morphismRestrict u U).paste_vert H)

end

end OAI.RepresentationTheory.Theta.Geometric.BaseChangeFunctionDescent

import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.AlgebraAutomorphismNaturality

/-! # Over Morphism Algebra -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OverMorphismAlgebra

noncomputable section

/-! Actual morphisms between affine schemes over a spectrum correspond
to algebra homomorphisms, retaining their literal scheme maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k A B : Type) [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

def affineOverMorphismAlgebra (f : EtaleSplittingAt.EtaleSplitting.affineOver k A ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B) : B →ₐ[k] A :=
  ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    (X := Opposite.op (CommAlgCat.of k A)) (Y := Opposite.op (CommAlgCat.of k B)) f).unop.hom

theorem affineOverMorphismAlgebra_spec (f : EtaleSplittingAt.EtaleSplitting.affineOver k A ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B) :
    Spec.map (CommRingCat.ofHom (affineOverMorphismAlgebra k A B f).toRingHom) = f.left := by
  change ((algSpec (CommRingCat.of k)).map
    ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      (X := Opposite.op (CommAlgCat.of k A)) (Y := Opposite.op (CommAlgCat.of k B)) f)).left = _
  exact congrArg Over.Hom.left ((algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage
    (X := Opposite.op (CommAlgCat.of k A)) (Y := Opposite.op (CommAlgCat.of k B)) f)

theorem affineOverMorphismAlgebra_recovery (f : EtaleSplittingAt.EtaleSplitting.affineOver k A ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B) :
    AlgebraAutomorphismNaturality.affineOverAlgHom k B A (affineOverMorphismAlgebra k A B f) = f := by
  apply Over.OverMorphism.ext
  exact affineOverMorphismAlgebra_spec k A B f

theorem affineOverMorphismAlgebra_ofAlgHom (f : B →ₐ[k] A) :
    affineOverMorphismAlgebra k A B (AlgebraAutomorphismNaturality.affineOverAlgHom k B A f) = f := by
  have hs : Spec.map (CommRingCat.ofHom
      (affineOverMorphismAlgebra k A B (AlgebraAutomorphismNaturality.affineOverAlgHom k B A f)).toRingHom) =
      Spec.map (CommRingCat.ofHom f.toRingHom) :=
    affineOverMorphismAlgebra_spec k A B (AlgebraAutomorphismNaturality.affineOverAlgHom k B A f)
  have h := congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  exact AlgHom.ext (fun b => RingHom.congr_fun h b)

def affineOverMorphismAlgebraEquiv : (EtaleSplittingAt.EtaleSplitting.affineOver k A ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B) ≃ (B →ₐ[k] A) where
  toFun := affineOverMorphismAlgebra k A B
  invFun := AlgebraAutomorphismNaturality.affineOverAlgHom k B A
  left_inv := affineOverMorphismAlgebra_recovery k A B
  right_inv := affineOverMorphismAlgebra_ofAlgHom k A B

theorem affineOverAlgHom_comp {D : Type} [CommRing D] [Algebra k D]
    (f : B →ₐ[k] A) (g : D →ₐ[k] B) :
    AlgebraAutomorphismNaturality.affineOverAlgHom k B A f ≫ AlgebraAutomorphismNaturality.affineOverAlgHom k D B g = AlgebraAutomorphismNaturality.affineOverAlgHom k D A (f.comp g) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
    Spec.map (CommRingCat.ofHom (f.comp g).toRingHom)
  rw [← Spec.map_comp]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OverMorphismAlgebra

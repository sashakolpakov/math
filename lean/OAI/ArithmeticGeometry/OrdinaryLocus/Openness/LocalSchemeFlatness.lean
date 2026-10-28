import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.RelativeBaseChange

/-! # Local Scheme Flatness -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LocalSchemeFlatness.Construction

noncomputable section

/-! The local scheme flatness criterion with an arbitrary finite source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry IsLocalRing
open scoped TensorProduct

universe u

/-- The finite-module flatness criterion for a finite scheme over a local
target. The closed fiber may be tested after a faithfully flat extension. -/
theorem flat_finite_over_local_of_flat_closedFiber_baseChange
    (R A D : Type u) [CommRing R] [CommRing A] [CommRing D]
    [Algebra R A] [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]
    [Algebra A D] [Algebra (A ⊗[R] ResidueField R) D]
    [IsScalarTower A (A ⊗[R] ResidueField R) D]
    [Module.FaithfullyFlat (A ⊗[R] ResidueField R) D]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsFinite f] [LocallyOfFinitePresentation f]
    [Flat (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)))]
    [Flat (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A D))))] :
    Flat f := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let B := Γ(X, ⊤)
  let φ : CommRingCat.of A ⟶ B := Spec.preimage (X.isoSpec.inv ≫ f)
  let : Algebra A B := φ.hom.toAlgebra
  let : Algebra R B := (φ.hom.comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  have hφ : Spec.map φ = X.isoSpec.inv ≫ f := Spec.map_preimage _
  have : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have : LocallyOfFinitePresentation (Spec.map φ) := by rw [hφ]; infer_instance
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
    have hc : Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map φ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
      rw [← Spec.map_comp]
      rfl
    rw [hc, hφ, Category.assoc]
    infer_instance
  let e : Over.mk (Spec.map φ) ≅ Over.mk f := Over.isoMk X.isoSpec.symm hφ.symm
  let i := Spec.map (CommRingCat.ofHom (algebraMap A D))
  have : Flat ((Over.pullback i).obj (Over.mk f)).hom :=
    inferInstanceAs (Flat (pullback.snd f i))
  have : Flat ((Over.pullback i).obj (Over.mk (Spec.map φ))).hom :=
    RelativeBaseChange.Construction.flat_of_overIso ((Over.pullback i).mapIso e)
  have : Flat (pullback.fst i (Spec.map φ)) :=
    (RelativeBaseChange.Construction.flat_pullback_fst_iff_snd i (Spec.map φ)).mpr
      (inferInstanceAs (Flat ((Over.pullback i).obj (Over.mk (Spec.map φ))).hom))
  have hfφ : Flat (Spec.map φ) :=
    AffineFiberFlatness.Construction.flat_SpecMap_of_flat_closedFiber_baseChange R A B D
  rw [hφ] at hfφ
  have : Flat (X.isoSpec.hom ≫ (X.isoSpec.inv ≫ f)) := inferInstance
  simpa only [Iso.hom_inv_id_assoc] using this

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LocalSchemeFlatness.Construction

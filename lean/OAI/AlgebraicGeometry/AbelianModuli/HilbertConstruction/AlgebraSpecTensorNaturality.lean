import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSpecTensorIso

/-! # Algebra Spec Tensor Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSpecTensorNaturality

noncomputable section

/-! Canonical scalar-extension presentations respect every algebra map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct

universe u

theorem algebraSpecTensorIso_natural
    {C D : Type u} [CommRing C] [CommRing D] [Algebra C D]
    {A B : CommAlgCat.{u} C} (φ : A ⟶ B) :
    (algSpec (.of D)).map ((AlgebraTensorFunctor.algebraTensorFunctor C D).map φ).op ≫
        (AlgebraSpecTensorIso.algebraSpecTensorIso C D A).hom =
      (AlgebraSpecTensorIso.algebraSpecTensorIso C D B).hom ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C D)))).map
          ((algSpec (.of C)).map φ.op) := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap C D))
  let a := Spec.map (CommRingCat.ofHom (algebraMap C A))
  let b := Spec.map (CommRingCat.ofHom (algebraMap C B))
  let t : Spec (.of (D ⊗[C] B)) ⟶ Spec (.of (D ⊗[C] A)) :=
    ((algSpec (.of D)).map ((AlgebraTensorFunctor.algebraTensorFunctor C D).map φ).op).left
  let eA : Spec (.of (D ⊗[C] A)) ⟶ pullback a c := (AlgebraSpecTensorIso.algebraSpecTensorIso C D A).hom.left
  let eB : Spec (.of (D ⊗[C] B)) ⟶ pullback b c := (AlgebraSpecTensorIso.algebraSpecTensorIso C D B).hom.left
  let f := (algSpec (.of C)).map φ.op
  let f₀ : Spec (.of B) ⟶ Spec (.of A) := f.left
  let fD : pullback b c ⟶ pullback a c := ((Over.pullback c).map f).left
  have heA : eA ≫ pullback.fst a c = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := C) (A := D) (B := A)).toRingHom) :=
    AlgebraSpecTensorIso.algebraSpecTensorIso_hom_fst C D A
  have heB : eB ≫ pullback.fst b c = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := C) (A := D) (B := B)).toRingHom) :=
    AlgebraSpecTensorIso.algebraSpecTensorIso_hom_fst C D B
  have hfD : fD ≫ pullback.fst a c = pullback.fst b c ≫ f₀ := pullback.lift_fst _ _ _
  apply Over.OverMorphism.ext
  change t ≫ eA = eB ≫ fD
  apply pullback.hom_ext
  · rw [Category.assoc, heA, Category.assoc, hfD, ← Category.assoc, heB]
    exact (NaturalTensorMapCartesian.naturalTensorMap_isPullback (R := D) φ.hom).w
  · exact (((algSpec (.of D)).map ((AlgebraTensorFunctor.algebraTensorFunctor C D).map φ).op ≫
      (AlgebraSpecTensorIso.algebraSpecTensorIso C D A).hom).w).trans
        (((AlgebraSpecTensorIso.algebraSpecTensorIso C D B).hom ≫ (Over.pullback c).map f).w).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSpecTensorNaturality

import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.Image
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentationRestriction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality

/-! # Image Augmentation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.ImageAugmentation.CechImage

noncomputable section

/-! The Čech direct-image comparison preserves actual restriction augmentations. -/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry Simplicial

universe u

theorem augmentation_along_isos {C : Type*} [Category* C] {A B D E S : C}
    (e : A ≅ B) (d : D ≅ B) (c : D ≅ E) (a : S ⟶ A) (b : S ⟶ D) (q : S ⟶ E)
    (h₁ : a ≫ e.hom = b ≫ d.hom) (h₂ : b ≫ c.hom = q) :
    a ≫ (e ≪≫ d.symm ≪≫ c).hom = q := by
  calc
    a ≫ (e ≪≫ d.symm ≪≫ c).hom = ((a ≫ e.hom) ≫ d.inv) ≫ c.hom := by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    _ = ((b ≫ d.hom) ≫ d.inv) ≫ c.hom := by rw [h₁]
    _ = b ≫ c.hom := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = q := h₂

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
  {ι : Type u} (U : ι → Y.Opens) (P : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X)

def pulledRestriction (n : SimplexCategory) : P ⟶
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj
      ((Image.CechImage.preimage f).op ⋙ AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X P)).obj n :=
  Pi.lift (fun t => AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restrictToIntersection R X P
    ((Image.CechImage.preimage f).obj (((FormalCoproduct.mk ι U).cech.obj (op n)).obj t)))

theorem opens_restriction (n : SimplexCategory) :
    pulledRestriction R f U P n ≫
        (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.componentIso (Image.CechImage.preimage f) U (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X P) n).hom =
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restriction R X (fun i => f ⁻¹ᵁ U i) P).app n := by
  let A := fun t : Fin (n.len + 1) → ι =>
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersection R X P ((Image.CechImage.preimage f).obj (∏ᶜ (U ∘ t)))
  let B := fun t : Fin (n.len + 1) → ι =>
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersection R X P (∏ᶜ (fun i => f ⁻¹ᵁ U (t i)))
  let a := fun t : Fin (n.len + 1) → ι =>
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restrictToIntersection R X P ((Image.CechImage.preimage f).obj (∏ᶜ (U ∘ t)))
  let b := fun t : Fin (n.len + 1) → ι =>
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X P).map
      (PreservesProduct.iso (Image.CechImage.preimage f) (U ∘ t)).symm.op.hom
  have h := AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentationRestriction.CechAugmentationRestriction.lift_comp_map A B a b
  exact h.trans (congrArg Pi.lift (funext fun t =>
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restrictToIntersection_map R X P
      (PreservesProduct.iso (Image.CechImage.preimage f) (U ∘ t)).symm.hom).symm))

theorem coefficient_restriction (n : SimplexCategory) :
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restriction R Y U ((Image.CechImage.functor R f).obj P)).app n ≫
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).map
          (Image.CechImage.coefficientsIso R f P).hom).app n =
      (Image.CechImage.functor R f).map (pulledRestriction R f U P n) ≫
        piComparison (Image.CechImage.functor R f) (fun t : Fin (n.len + 1) → ι =>
          AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersection R X P ((Image.CechImage.preimage f).obj (∏ᶜ (U ∘ t)))) := by
  let A := fun t : Fin (n.len + 1) → ι =>
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersection R Y ((Image.CechImage.functor R f).obj P) (∏ᶜ (U ∘ t))
  let B := fun t : Fin (n.len + 1) → ι =>
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersection R X P ((Image.CechImage.preimage f).obj (∏ᶜ (U ∘ t)))
  let a := fun t : Fin (n.len + 1) → ι =>
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restrictToIntersection R Y ((Image.CechImage.functor R f).obj P) (∏ᶜ (U ∘ t))
  have h₁ := AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentationRestriction.CechAugmentationRestriction.lift_comp_map A (fun t => (Image.CechImage.functor R f).obj (B t)) a
    (fun t => (Image.CechImage.coefficientsIso R f P).hom.app (op (∏ᶜ (U ∘ t))))
  have h₂ := AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentationRestriction.CechAugmentationRestriction.map_lift_comp_piComparison (Image.CechImage.functor R f) B
    (fun t => AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restrictToIntersection R X P ((Image.CechImage.preimage f).obj (∏ᶜ (U ∘ t))))
  exact h₁.trans ((congrArg Pi.lift (funext fun _ => Category.comp_id _)).trans h₂.symm)

theorem restriction_zero :
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restriction R Y U ((Image.CechImage.functor R f).obj P)).app ⦋0⦌ ≫ (Image.CechImage.complexIso R f U P).hom.f 0 =
      (Image.CechImage.functor R f).map ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restriction R X (fun i => f ⁻¹ᵁ U i) P).app ⦋0⦌) := by
  let G := Image.CechImage.functor R f
  let E := (FormalCoproduct.mk ι U).cech
  let T := HomologicalComplex.eval (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R Y) (.up ℕ) 0
  let e := T.mapIso ((cechComplexFunctor U).mapIso (Image.CechImage.coefficientsIso R f P))
  let d := T.mapIso (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G E
    ((Image.CechImage.preimage f).op ⋙ AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X P))
  let c := T.mapIso ((G.mapHomologicalComplex (.up ℕ)).mapIso
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (Image.CechImage.preimage f) U (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X P)))
  let b := G.map (pulledRestriction R f U P ⦋0⦌)
  have h₁ : (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restriction R Y U (G.obj P)).app ⦋0⦌ ≫ e.hom = b ≫ d.hom :=
    (coefficient_restriction R f U P ⦋0⦌).trans
      (congrArg (fun k => b ≫ k) (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.hom_f G E
        ((Image.CechImage.preimage f).op ⋙ AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X P) 0).symm)
  have h₂ : b ≫ c.hom = G.map ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restriction R X (fun i => f ⁻¹ᵁ U i) P).app ⦋0⦌) :=
    (G.map_comp _ _).symm.trans (congrArg G.map (opens_restriction R f U P ⦋0⦌))
  exact augmentation_along_isos e d c _ b _ h₁ h₂

theorem augmentation :
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.augmentation R Y U ((Image.CechImage.functor R f).obj P) ≫ (Image.CechImage.complexIso R f U P).hom =
      (HomologicalComplex.singleMapHomologicalComplex (Image.CechImage.functor R f) (.up ℕ) 0).inv.app P ≫
        ((Image.CechImage.functor R f).mapHomologicalComplex (.up ℕ)).map
          (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.augmentation R X (fun i => f ⁻¹ᵁ U i) P) := by
  apply HomologicalComplex.from_single_hom_ext
  let G := Image.CechImage.functor R f
  change (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.augmentation R Y U (G.obj P)).f 0 ≫ (Image.CechImage.complexIso R f U P).hom.f 0 =
    𝟙 _ ≫ G.map ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.augmentation R X (fun i => f ⁻¹ᵁ U i) P).f 0)
  exact (congrArg (fun k => k ≫ (Image.CechImage.complexIso R f U P).hom.f 0)
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.Augmentation.CechAugmentation.augmentation_f_zero R Y U (G.obj P))).trans
      ((restriction_zero R f U P).trans
        ((congrArg G.map (AlgebraicGeometry.Crystalline.Cohomology.Cech.Augmentation.CechAugmentation.augmentation_f_zero R X (fun i => f ⁻¹ᵁ U i) P)).symm.trans
          (Category.id_comp _).symm))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.ImageAugmentation.CechImage

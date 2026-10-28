import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Augmentation

/-! # Augmentation Restriction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.AugmentationRestriction.MixedCechAugmentationRestriction

noncomputable section

/-!
Mixed-universe version for the native crystalline coefficient modules.

# Restricting the canonical Čech augmentation

The comparison of Čech complexes under an open immersion carries the
canonical restriction augmentation to the local canonical augmentation.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry Simplicial

universe u v

theorem map_lift_comp_piComparison {A B : Type*} [Category A] [Category B]
    [HasProducts.{u} A] [HasProducts.{u} B] (G : A ⥤ B)
    {ι : Type u} {P : A} (X : ι → A) (f : ∀ i, P ⟶ X i) :
    G.map (Pi.lift f) ≫ piComparison G X = Pi.lift (fun i => G.map (f i)) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, piComparison_comp_π, ← G.map_comp, Pi.lift_comp_π]

theorem lift_comp_map {A : Type*} [Category A] [HasProducts.{u} A]
    {ι : Type u} {P : A} (X Y : ι → A) (a : ∀ i, P ⟶ X i) (b : ∀ i, X i ⟶ Y i) :
    Pi.lift a ≫ Limits.Pi.map b = Pi.lift (fun i => a i ≫ b i) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, Pi.map_π, Pi.lift_comp_π_assoc, Pi.lift_comp_π]

theorem map_lift_comp_maps {A B : Type*} [Category A] [Category B]
    [HasProducts.{u} A] [HasProducts.{u} B] (G : A ⥤ B)
    {ι : Type u} {P : A} (X : ι → A) (Y Z : ι → B)
    (a : ∀ i, P ⟶ X i) (b : ∀ i, G.obj (X i) ⟶ Y i) (e : ∀ i, Y i ≅ Z i) :
    G.map (Pi.lift a) ≫ ((𝟙 _ ≫ piComparison G X) ≫ Limits.Pi.map b ≫ (Pi.mapIso e).hom) =
      Pi.lift (fun i => G.map (a i) ≫ b i ≫ (e i).hom) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, Category.id_comp, Pi.mapIso_hom_π, Pi.map_π_assoc,
    piComparison_comp_π_assoc, Pi.lift_comp_π]
  rw [← Category.assoc, ← G.map_comp, Pi.lift_comp_π]

variable (R : Type v) [CommRing R] {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
  (P : Presheaf.MixedCechPresheaf.Presheaves R X) {ι : Type u} (U : ι → X.Opens)

theorem restriction_comp_iso_zero :
    (CechRestriction.MixedCechRestriction.restrictionFunctor R f).map ((Presheaf.MixedCechPresheaf.restriction R X U P).app ⦋0⦌) ≫
      (CechRestriction.MixedCechRestriction.complexIso R f P U).hom.f 0 =
        (Presheaf.MixedCechPresheaf.restriction R Y (fun i => f ⁻¹ᵁ U i)
          ((CechRestriction.MixedCechRestriction.restrictionFunctor R f).obj P)).app ⦋0⦌ := by
  dsimp only [CechRestriction.MixedCechRestriction.complexIso, Iso.trans_hom, HomologicalComplex.comp_f,
    Cech.CoefficientChange.CechCoefficientChange.complexIso, Cech.CoefficientChange.CechCoefficientChange.mapCofaceIso,
    Cech.BaseChange.CechBaseChange.complexIso]
  let G := CechRestriction.MixedCechRestriction.restrictionFunctor R f
  let A := (FormalCoproduct.mk ι U).cech.obj (op ⦋0⦌)
  let B := (FormalCoproduct.mk ι (fun i => f ⁻¹ᵁ U i)).cech.obj (op ⦋0⦌)
  change G.map (Pi.lift (fun t : A.I => Presheaf.MixedCechPresheaf.restrictToIntersection R X P (A.obj t))) ≫
    ((𝟙 _ ≫ piComparison G (fun t : A.I => Presheaf.MixedCechPresheaf.intersection R X P (A.obj t))) ≫
      Limits.Pi.map (fun t : A.I => (CechRestriction.MixedCechRestriction.coefficientsIso R f P).hom.app (op (A.obj t))) ≫
        (Cech.BaseChange.CechBaseChange.componentIso (CechRestriction.MixedCechRestriction.preimageFunctor f) U
          (Presheaf.MixedCechPresheaf.intersectionCoefficients R Y (G.obj P)) ⦋0⦌).hom) =
    Pi.lift (fun t : B.I => Presheaf.MixedCechPresheaf.restrictToIntersection R Y (G.obj P) (B.obj t))
  refine (map_lift_comp_maps G
    (fun t : Fin 1 → ι => Presheaf.MixedCechPresheaf.intersection R X P (∏ᶜ (U ∘ t)))
    (fun t : Fin 1 → ι => Presheaf.MixedCechPresheaf.intersection R Y (G.obj P) (f ⁻¹ᵁ (∏ᶜ (U ∘ t))))
    (fun t : Fin 1 → ι => Presheaf.MixedCechPresheaf.intersection R Y (G.obj P) (∏ᶜ (fun i => f ⁻¹ᵁ U (t i))))
    (fun t => Presheaf.MixedCechPresheaf.restrictToIntersection R X P (∏ᶜ (U ∘ t)))
    (fun t => (CechRestriction.MixedCechRestriction.coefficientsIso R f P).hom.app (op (∏ᶜ (U ∘ t))))
    (fun t => (Presheaf.MixedCechPresheaf.intersectionCoefficients R Y (G.obj P)).mapIso
      (PreservesProduct.iso (CechRestriction.MixedCechRestriction.preimageFunctor f) (U ∘ t)).symm.op)).trans ?_
  congr 1
  funext t
  apply NatTrans.ext
  funext V
  change P.map _ ≫ P.map _ ≫ P.map _ = P.map _
  rw [← P.map_comp, ← P.map_comp]
  congr 1

theorem from_mapped_single_hom_ext {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] [HasZeroObject A] [HasZeroObject B]
    (G : A ⥤ B) [G.Additive] (P : A) {K : CochainComplex B ℕ}
    (φ ψ : ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((CochainComplex.single₀ A).obj P)) ⟶ K) (h : φ.f 0 = ψ.f 0) : φ = ψ := by
  ext n : 1
  by_cases hn : n = 0
  · subst n
    exact h
  · exact (G.map_isZero (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℕ) 0 P n hn)).eq_of_src _ _

/-- The restriction comparison preserves the canonical augmentation as a map of complexes. -/
theorem augmentation_comp_iso :
    ((CechRestriction.MixedCechRestriction.restrictionFunctor R f).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (Presheaf.MixedCechPresheaf.augmentation R X U P) ≫ (CechRestriction.MixedCechRestriction.complexIso R f P U).hom =
        ((HomologicalComplex.singleMapHomologicalComplex (CechRestriction.MixedCechRestriction.restrictionFunctor R f)
          (ComplexShape.up ℕ) 0).hom.app P) ≫
            Presheaf.MixedCechPresheaf.augmentation R Y (fun i => f ⁻¹ᵁ U i)
              ((CechRestriction.MixedCechRestriction.restrictionFunctor R f).obj P) := by
  apply from_mapped_single_hom_ext
  change (CechRestriction.MixedCechRestriction.restrictionFunctor R f).map ((Presheaf.MixedCechPresheaf.augmentation R X U P).f 0) ≫
    (CechRestriction.MixedCechRestriction.complexIso R f P U).hom.f 0 =
      𝟙 _ ≫ (Presheaf.MixedCechPresheaf.augmentation R Y (fun i => f ⁻¹ᵁ U i)
        ((CechRestriction.MixedCechRestriction.restrictionFunctor R f).obj P)).f 0
  refine (congrArg (fun a => (CechRestriction.MixedCechRestriction.restrictionFunctor R f).map a ≫
    (CechRestriction.MixedCechRestriction.complexIso R f P U).hom.f 0)
      (Augmentation.MixedCechAugmentation.augmentation_f_zero R X U P)).trans ?_
  exact (restriction_comp_iso_zero R f P U).trans
    ((Augmentation.MixedCechAugmentation.augmentation_f_zero R Y (fun i => f ⁻¹ᵁ U i)
      ((CechRestriction.MixedCechRestriction.restrictionFunctor R f).obj P)).symm.trans (Category.id_comp _).symm)

theorem restricted_augmentation_quasiIso (i : ι) :
    QuasiIso (((CechRestriction.MixedCechRestriction.restrictionFunctor R (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (Presheaf.MixedCechPresheaf.augmentation R X U P)) := by
  let G := CechRestriction.MixedCechRestriction.restrictionFunctor R (U i).ι
  let a := Presheaf.MixedCechPresheaf.augmentation R X U P
  let b := Presheaf.MixedCechPresheaf.augmentation R (U i).toScheme (Cech.Contraction.CechContraction.restrictedFamily X U i)
    (G.obj P)
  have : QuasiIso b := Augmentation.MixedCechAugmentation.split_quasiIso R (U i).toScheme
    (Cech.Contraction.CechContraction.restrictedFamily X U i) (G.obj P) i (Cech.Contraction.CechContraction.restrictedFamily_self X U i)
  have : IsIso ((HomologicalComplex.singleMapHomologicalComplex G
    (ComplexShape.up ℕ) 0).hom.app P) := inferInstance
  have hcomp : QuasiIso (((HomologicalComplex.singleMapHomologicalComplex G
    (ComplexShape.up ℕ) 0).hom.app P) ≫ b) := quasiIso_comp _ b
  have h : (G.mapHomologicalComplex (ComplexShape.up ℕ)).map a ≫
      (CechRestriction.MixedCechRestriction.complexIso R (U i).ι P U).hom =
        ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).hom.app P) ≫ b :=
    augmentation_comp_iso R (U i).ι P U
  have : QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map a ≫
      (CechRestriction.MixedCechRestriction.complexIso R (U i).ι P U).hom) := h.symm ▸ hcomp
  exact (quasiIso_iff_comp_right ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map a)
    (CechRestriction.MixedCechRestriction.complexIso R (U i).ι P U).hom).mp inferInstance

def restrictedHomotopyEquiv (i : ι) :=
  (HomotopyEquiv.ofIso ((HomologicalComplex.singleMapHomologicalComplex
    (CechRestriction.MixedCechRestriction.restrictionFunctor R (U i).ι) (ComplexShape.up ℕ) 0).app P)).trans
      (CechRestriction.MixedCechRestriction.coverMemberHomotopyEquiv R P U i)

theorem restrictedHomotopyHom (i : ι) :
    (restrictedHomotopyEquiv R P U i).hom =
      ((CechRestriction.MixedCechRestriction.restrictionFunctor R (U i).ι).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (Presheaf.MixedCechPresheaf.augmentation R X U P) := by
  let G := CechRestriction.MixedCechRestriction.restrictionFunctor R (U i).ι
  let s := ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).app P).hom
  let e := CechRestriction.MixedCechRestriction.complexIso R (U i).ι P U
  change s ≫ ((PresheafContraction.MixedCechPresheafContraction.localHomotopyEquiv R X U P i).hom ≫ e.inv) = _
  refine (congrArg (fun b => s ≫ (b ≫ e.inv))
    (Augmentation.MixedCechAugmentation.homotopyHom_eq_augmentation R (U i).toScheme
      (Cech.Contraction.CechContraction.restrictedFamily X U i) (G.obj P) i
        (Cech.Contraction.CechContraction.restrictedFamily_self X U i))).trans ?_
  refine (Category.assoc s (Presheaf.MixedCechPresheaf.augmentation R (U i).toScheme
    (Cech.Contraction.CechContraction.restrictedFamily X U i) (G.obj P)) e.inv).symm.trans ?_
  exact e.comp_inv_eq.mpr (augmentation_comp_iso R (U i).ι P U).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.AugmentationRestriction.MixedCechAugmentationRestriction

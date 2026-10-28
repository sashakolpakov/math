import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Augmentation

/-! # Augmentation Restriction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentationRestriction.CechAugmentationRestriction

noncomputable section

/-!
# Restricting the canonical Čech augmentation

The comparison of Čech complexes under an open immersion carries the
canonical restriction augmentation to the local canonical augmentation.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry Simplicial

universe u

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

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
  (P : Presheaf.CechPresheaf.Presheaves R X) {ι : Type u} (U : ι → X.Opens)

theorem restriction_comp_iso_zero :
    (Cover.CechRestriction.restrictionFunctor R f).map ((Presheaf.CechPresheaf.restriction R X U P).app ⦋0⦌) ≫
      (Cover.CechRestriction.complexIso R f P U).hom.f 0 =
        (Presheaf.CechPresheaf.restriction R Y (fun i => f ⁻¹ᵁ U i)
          ((Cover.CechRestriction.restrictionFunctor R f).obj P)).app ⦋0⦌ := by
  dsimp only [Cover.CechRestriction.complexIso, Iso.trans_hom, HomologicalComplex.comp_f,
    CoefficientChange.CechCoefficientChange.complexIso, CoefficientChange.CechCoefficientChange.mapCofaceIso,
    BaseChange.CechBaseChange.complexIso]
  let G := Cover.CechRestriction.restrictionFunctor R f
  let A := (FormalCoproduct.mk ι U).cech.obj (op ⦋0⦌)
  let B := (FormalCoproduct.mk ι (fun i => f ⁻¹ᵁ U i)).cech.obj (op ⦋0⦌)
  change G.map (Pi.lift (fun t : A.I => Presheaf.CechPresheaf.restrictToIntersection R X P (A.obj t))) ≫
    ((𝟙 _ ≫ piComparison G (fun t : A.I => Presheaf.CechPresheaf.intersection R X P (A.obj t))) ≫
      Limits.Pi.map (fun t : A.I => (Cover.CechRestriction.coefficientsIso R f P).hom.app (op (A.obj t))) ≫
        (BaseChange.CechBaseChange.componentIso (Cover.CechRestriction.preimageFunctor f) U
          (Presheaf.CechPresheaf.intersectionCoefficients R Y (G.obj P)) ⦋0⦌).hom) =
    Pi.lift (fun t : B.I => Presheaf.CechPresheaf.restrictToIntersection R Y (G.obj P) (B.obj t))
  refine (map_lift_comp_maps G
    (fun t : Fin 1 → ι => Presheaf.CechPresheaf.intersection R X P (∏ᶜ (U ∘ t)))
    (fun t : Fin 1 → ι => Presheaf.CechPresheaf.intersection R Y (G.obj P) (f ⁻¹ᵁ (∏ᶜ (U ∘ t))))
    (fun t : Fin 1 → ι => Presheaf.CechPresheaf.intersection R Y (G.obj P) (∏ᶜ (fun i => f ⁻¹ᵁ U (t i))))
    (fun t => Presheaf.CechPresheaf.restrictToIntersection R X P (∏ᶜ (U ∘ t)))
    (fun t => (Cover.CechRestriction.coefficientsIso R f P).hom.app (op (∏ᶜ (U ∘ t))))
    (fun t => (Presheaf.CechPresheaf.intersectionCoefficients R Y (G.obj P)).mapIso
      (PreservesProduct.iso (Cover.CechRestriction.preimageFunctor f) (U ∘ t)).symm.op)).trans ?_
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
    ((Cover.CechRestriction.restrictionFunctor R f).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (Presheaf.CechPresheaf.augmentation R X U P) ≫ (Cover.CechRestriction.complexIso R f P U).hom =
        ((HomologicalComplex.singleMapHomologicalComplex (Cover.CechRestriction.restrictionFunctor R f)
          (ComplexShape.up ℕ) 0).hom.app P) ≫
            Presheaf.CechPresheaf.augmentation R Y (fun i => f ⁻¹ᵁ U i)
              ((Cover.CechRestriction.restrictionFunctor R f).obj P) := by
  apply from_mapped_single_hom_ext
  change (Cover.CechRestriction.restrictionFunctor R f).map ((Presheaf.CechPresheaf.augmentation R X U P).f 0) ≫
    (Cover.CechRestriction.complexIso R f P U).hom.f 0 =
      𝟙 _ ≫ (Presheaf.CechPresheaf.augmentation R Y (fun i => f ⁻¹ᵁ U i)
        ((Cover.CechRestriction.restrictionFunctor R f).obj P)).f 0
  refine (congrArg (fun a => (Cover.CechRestriction.restrictionFunctor R f).map a ≫
    (Cover.CechRestriction.complexIso R f P U).hom.f 0)
      (Augmentation.CechAugmentation.augmentation_f_zero R X U P)).trans ?_
  exact (restriction_comp_iso_zero R f P U).trans
    ((Augmentation.CechAugmentation.augmentation_f_zero R Y (fun i => f ⁻¹ᵁ U i)
      ((Cover.CechRestriction.restrictionFunctor R f).obj P)).symm.trans (Category.id_comp _).symm)

theorem restricted_augmentation_quasiIso (i : ι) :
    QuasiIso (((Cover.CechRestriction.restrictionFunctor R (U i).ι).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (Presheaf.CechPresheaf.augmentation R X U P)) := by
  let G := Cover.CechRestriction.restrictionFunctor R (U i).ι
  let a := Presheaf.CechPresheaf.augmentation R X U P
  let b := Presheaf.CechPresheaf.augmentation R (U i).toScheme (Contraction.CechContraction.restrictedFamily X U i)
    (G.obj P)
  have : QuasiIso b := Augmentation.CechAugmentation.split_quasiIso R (U i).toScheme
    (Contraction.CechContraction.restrictedFamily X U i) (G.obj P) i (Contraction.CechContraction.restrictedFamily_self X U i)
  have : IsIso ((HomologicalComplex.singleMapHomologicalComplex G
    (ComplexShape.up ℕ) 0).hom.app P) := inferInstance
  have hcomp : QuasiIso (((HomologicalComplex.singleMapHomologicalComplex G
    (ComplexShape.up ℕ) 0).hom.app P) ≫ b) := quasiIso_comp _ b
  have h : (G.mapHomologicalComplex (ComplexShape.up ℕ)).map a ≫
      (Cover.CechRestriction.complexIso R (U i).ι P U).hom =
        ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).hom.app P) ≫ b :=
    augmentation_comp_iso R (U i).ι P U
  have : QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map a ≫
      (Cover.CechRestriction.complexIso R (U i).ι P U).hom) := h.symm ▸ hcomp
  exact (quasiIso_iff_comp_right ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map a)
    (Cover.CechRestriction.complexIso R (U i).ι P U).hom).mp inferInstance

def restrictedHomotopyEquiv (i : ι) :=
  (HomotopyEquiv.ofIso ((HomologicalComplex.singleMapHomologicalComplex
    (Cover.CechRestriction.restrictionFunctor R (U i).ι) (ComplexShape.up ℕ) 0).app P)).trans
      (Cover.CechRestriction.coverMemberHomotopyEquiv R P U i)

theorem restrictedHomotopyHom (i : ι) :
    (restrictedHomotopyEquiv R P U i).hom =
      ((Cover.CechRestriction.restrictionFunctor R (U i).ι).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (Presheaf.CechPresheaf.augmentation R X U P) := by
  let G := Cover.CechRestriction.restrictionFunctor R (U i).ι
  let s := ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).app P).hom
  let e := Cover.CechRestriction.complexIso R (U i).ι P U
  change s ≫ ((PresheafContraction.CechPresheafContraction.localHomotopyEquiv R X U P i).hom ≫ e.inv) = _
  refine (congrArg (fun b => s ≫ (b ≫ e.inv))
    (Augmentation.CechAugmentation.homotopyHom_eq_augmentation R (U i).toScheme
      (Contraction.CechContraction.restrictedFamily X U i) (G.obj P) i
        (Contraction.CechContraction.restrictedFamily_self X U i))).trans ?_
  refine (Category.assoc s (Presheaf.CechPresheaf.augmentation R (U i).toScheme
    (Contraction.CechContraction.restrictedFamily X U i) (G.obj P)) e.inv).symm.trans ?_
  exact e.comp_inv_eq.mpr (augmentation_comp_iso R (U i).ι P U).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentationRestriction.CechAugmentationRestriction

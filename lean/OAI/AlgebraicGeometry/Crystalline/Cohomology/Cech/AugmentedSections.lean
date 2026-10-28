import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.SectionsExactness
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CochainAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizedLeft

/-! # Augmented Sections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections.CechAugmentedSections

noncomputable section

/-!
# The canonical augmentation on Čech sections

The already constructed Čech augmentation identifies sections with
zero-cocycles on a cover member. Left exactness descends to global
sections when coefficients and zero-cochains localize on that cover.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  {ι : Type u} (U : ι → X.Opens) (P : Presheaf.CechPresheaf.Presheaves R X)

def presheafInitial : ShortComplex (Presheaf.CechPresheaf.Presheaves R X) :=
  CochainAugmentation.CochainAugmentationCriterion.initialShort (Presheaf.CechPresheaf.augmentation R X U P)
    (HomologicalComplex.single_obj_d _ _ _ _ _)

def initial (V : X.Opens) : ShortComplex (ModuleCat.{u} R) :=
  (presheafInitial R X U P).map ((evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).obj (op V))

def restriction (V : X.Opens) : initial R X U P ⊤ ⟶ initial R X U P V :=
  (presheafInitial R X U P).mapNatTrans
    ((evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).map V.leTop.op)

def augmentation (V : X.Opens) :=
  (((evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).obj (op V)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (Presheaf.CechPresheaf.augmentation R X U P)

theorem member_leftExact (i : ι) :
    (initial R X U P (U i)).Exact ∧ Mono (initial R X U P (U i)).f := by
  let G := Cover.CechRestriction.restrictionFunctor R (U i).ι
  let E := (evaluation (U i).toScheme.Opensᵒᵖ (ModuleCat.{u} R)).obj (op ⊤)
  let a := (G.mapHomologicalComplex (ComplexShape.up ℕ)).map (Presheaf.CechPresheaf.augmentation R X U P)
  have ha : QuasiIso a := AugmentationRestriction.CechAugmentationRestriction.restricted_augmentation_quasiIso R P U i
  have hK : ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((CochainComplex.single₀ (Presheaf.CechPresheaf.Presheaves R X)).obj P)).d 0 1 = 0 := by
    exact (congrArg G.map (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 P 0 1)).trans
      (G.map_zero _ _)
  have hi : ((presheafInitial R X U P).map G).Exact ∧
      Mono ((presheafInitial R X U P).map G).f :=
    (CochainAugmentation.CochainAugmentationCriterion.quasiIsoAt_zero_iff a hK).mp (ha.quasiIsoAt 0)
  have hm : Mono ((presheafInitial R X U P).map G).f := hi.2
  have he : (((presheafInitial R X U P).map G).map E).Exact ∧
      Mono (((presheafInitial R X U P).map G).map E).f :=
    ⟨hi.1.map E, by change Mono (E.map ((presheafInitial R X U P).map G).f); infer_instance⟩
  change (initial R X U P ((U i).ι ''ᵁ ⊤)).Exact ∧
    Mono (initial R X U P ((U i).ι ''ᵁ ⊤)).f at he
  rwa [Scheme.Opens.ι_image_top] at he

theorem global_leftExact (s : ι → R) (hs : Ideal.span (Set.range s) = ⊤)
    [∀ i, IsLocalizedModule (Submonoid.powers (s i)) (P.map (U i).leTop.op).hom]
    [∀ i, IsLocalizedModule (Submonoid.powers (s i))
      ((SectionsExactness.CechSectionsExactness.restriction R X U P (U i)).f 0).hom] :
    (initial R X U P ⊤).Exact ∧ Mono (initial R X U P ⊤).f := by
  have : ∀ i, IsLocalizedModule (Submonoid.powers (s i))
      ((restriction R X U P (U i)).τ₁).hom := by
    intro i
    change IsLocalizedModule (Submonoid.powers (s i)) (P.map (U i).leTop.op).hom
    infer_instance
  have : ∀ i, IsLocalizedModule (Submonoid.powers (s i))
      ((restriction R X U P (U i)).τ₂).hom := by
    intro i
    change IsLocalizedModule (Submonoid.powers (s i))
      ((SectionsExactness.CechSectionsExactness.restriction R X U P (U i)).f 0).hom
    infer_instance
  exact LocalizedLeft.LocalizedLeftExactness.leftExact R ι s hs (initial R X U P ⊤)
    (fun i => initial R X U P (U i)) (fun i => restriction R X U P (U i))
    (fun i => member_leftExact R X U P i)

theorem quasiIsoAt_zero_iff (V : X.Opens) :
    QuasiIsoAt (augmentation R X U P V) 0 ↔
      (initial R X U P V).Exact ∧ Mono (initial R X U P V).f := by
  exact CochainAugmentation.CochainAugmentationCriterion.quasiIsoAt_zero_iff (augmentation R X U P V) (by
    let E := (evaluation X.Opensᵒᵖ (ModuleCat.{u} R)).obj (op V)
    exact (congrArg E.map (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 P 0 1)).trans
      (E.map_zero _ _))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections.CechAugmentedSections

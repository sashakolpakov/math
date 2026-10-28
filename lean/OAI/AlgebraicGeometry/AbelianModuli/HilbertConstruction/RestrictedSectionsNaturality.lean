import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InjectiveOpenSectionsCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicResolutionNaturality

/-! # Restricted Sections Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictedSectionsNaturality.IntrinsicCech

noncomputable section

/-! Evaluation on an open is naturally the global-section evaluation after restriction. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : TopCat.{u}}

def sheafRestrictionTopEvaluationIso (V : Opens X) :
    TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat.{u} V.isOpenEmbedding ⋙ AcyclicResolutionCohomology.IntrinsicCech.sheafTopEvaluation (TopCat.of V) ≅
      InjectiveOpenSectionsCohomology.IntrinsicCech.sheafOpenEvaluation X V := by
  change InjectiveOpenSectionsCohomology.IntrinsicCech.sheafOpenEvaluation X (V.isOpenEmbedding.functor.obj ⊤) ≅ InjectiveOpenSectionsCohomology.IntrinsicCech.sheafOpenEvaluation X V
  rw [Opens.isOpenEmbedding_obj_top V]

def restrictedTopSectionsComplexIso
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ) (V : Opens X) :
    AcyclicResolutionCohomology.IntrinsicCech.sheafTopSectionsComplex
        (((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat.{u} V.isOpenEmbedding).mapHomologicalComplex (.up ℕ)).obj K) ≅
      ((InjectiveOpenSectionsCohomology.IntrinsicCech.sheafOpenEvaluation X V).mapHomologicalComplex (.up ℕ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (sheafRestrictionTopEvaluationIso V).app (K.X i))
    (fun i j _ => ((sheafRestrictionTopEvaluationIso V).hom.naturality (K.d i j)).symm)

theorem restrictedTopSectionsComplexIso_naturality
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ} (ψ : K ⟶ L) (V : Opens X) :
    ((InjectiveOpenSectionsCohomology.IntrinsicCech.sheafOpenEvaluation X V).mapHomologicalComplex (.up ℕ)).map ψ ≫
        (restrictedTopSectionsComplexIso L V).inv =
      (restrictedTopSectionsComplexIso K V).inv ≫ SectionsHomologyNaturality.IntrinsicCech.sheafTopSectionsMap
        (((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat.{u} V.isOpenEmbedding).mapHomologicalComplex (.up ℕ)).map ψ) :=
  by
    apply HomologicalComplex.Hom.ext
    funext i
    exact (sheafRestrictionTopEvaluationIso V).inv.naturality (ψ.f i)

def chosenSheafResolutionMap {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    (injectiveResolution F).cocomplex ⟶ (injectiveResolution G).cocomplex :=
  InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F)

theorem chosenSheafResolutionMap_aug {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    f ≫ (injectiveResolution G).ι.f 0 =
      (injectiveResolution F).ι.f 0 ≫ (chosenSheafResolutionMap f).f 0 :=
  (InjectiveResolution.desc_commutes_zero f (injectiveResolution G) (injectiveResolution F)).symm

def injectiveOpenSectionsMap {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (V : Opens X) : InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex F V ⟶ InjectiveOpenSectionsCohomology.IntrinsicCech.injectiveOpenSectionsComplex G V :=
  ((InjectiveOpenSectionsCohomology.IntrinsicCech.sheafOpenEvaluation X V).mapHomologicalComplex (.up ℕ)).map (chosenSheafResolutionMap f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictedSectionsNaturality.IntrinsicCech

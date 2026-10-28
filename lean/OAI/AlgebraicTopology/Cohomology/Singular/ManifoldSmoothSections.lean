import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf
import OAI.AlgebraicTopology.DeRham.Comparison.CechComplexAugmentation

/-! # Manifold Smooth Sections -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSections

noncomputable section

/-!
# Actual sections of the smooth singular cochain presheaf

Evaluation on an open set is its genuine smooth singular cochain complex.
At the top open set, the canonical smooth identification with the ambient
manifold gives the corresponding cochain isomorphism.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.DeRham.Comparison.CechComplexAugmentation
open scoped _root_.Manifold ContDiff

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (X : Type) [TopologicalSpace X] [ChartedSpace E X]
variable (A : ModuleCat.{0} ℂ)

/-- Evaluation of the actual smooth presheaf complex on an open set. -/
def manifoldSmoothPresheafSectionsIso (W : Opens X) :
    DeRham.Comparison.CechComplexAugmentation.presheafComplexSections W (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E X A) ≅
      ManifoldSmooth.manifoldSmoothCochains E A W :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

@[simp]
theorem manifoldSmoothPresheafSectionsIso_hom_f (W : Opens X) (n : ℕ) :
    (manifoldSmoothPresheafSectionsIso E X A W).hom.f n = 𝟙 _ := rfl

@[simp]
theorem manifoldSmoothPresheafSectionsIso_inv_f (W : Opens X) (n : ℕ) :
    (manifoldSmoothPresheafSectionsIso E X A W).inv.f n = 𝟙 _ := rfl

/-- The canonical map to the top open subset is smooth for the actual
inherited charted-space structure. -/
theorem contMDiff_manifoldTopLift :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun x : X => (⟨x, by trivial⟩ : (⊤ : Opens X))) := by
  apply (ContMDiff.subtypeVal_comp_iff (⊤ : Opens X) _).mp
  exact contMDiff_id

/-- Smooth cochains on the top open subset identify canonically with
smooth cochains on the original manifold. -/
def manifoldSmoothCochainsTopIso :
    ManifoldSmooth.manifoldSmoothCochains E A (⊤ : Opens X) ≅ ManifoldSmooth.manifoldSmoothCochains E A X where
  hom := ManifoldSmoothFunctor.manifoldSmoothPullback E E A
    (fun x : X => (⟨x, by trivial⟩ : (⊤ : Opens X))) (contMDiff_manifoldTopLift E X)
  inv := ManifoldSmoothFunctor.manifoldSmoothPullback E E A (Subtype.val : (⊤ : Opens X) → X)
    (contMDiff_subtype_val (I := 𝓘(ℝ, E)))
  hom_inv_id := by
    rw [← ManifoldSmoothFunctor.manifoldSmoothPullback_comp]
    exact ManifoldSmoothFunctor.manifoldSmoothPullback_id A
  inv_hom_id := by
    rw [← ManifoldSmoothFunctor.manifoldSmoothPullback_comp]
    exact ManifoldSmoothFunctor.manifoldSmoothPullback_id A

/-- Actual top sections identified with smooth cochains on the ambient
manifold, using the canonical smooth top-open identification. -/
def manifoldSmoothPresheafTopIso :
    DeRham.Comparison.CechComplexAugmentation.presheafComplexSections (⊤ : Opens X) (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E X A) ≅
      ManifoldSmooth.manifoldSmoothCochains E A X :=
  manifoldSmoothPresheafSectionsIso E X A ⊤ ≪≫ manifoldSmoothCochainsTopIso E X A

/-- The inverse top-section identification is literal pullback along the
inclusion of the top open subset. -/
theorem manifoldSmoothPresheafTopIso_inv :
    (manifoldSmoothPresheafTopIso E X A).inv =
      ManifoldSmoothFunctor.manifoldSmoothPullback E E A (Subtype.val : (⊤ : Opens X) → X)
        (contMDiff_subtype_val (I := 𝓘(ℝ, E))) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [manifoldSmoothPresheafTopIso, Iso.trans_inv, HomologicalComplex.comp_f,
    manifoldSmoothPresheafSectionsIso_inv_f, Category.comp_id]
  rfl

/-- The forward identification pulls back along the canonical lift into
the top open subset. -/
theorem manifoldSmoothPresheafTopIso_hom :
    (manifoldSmoothPresheafTopIso E X A).hom =
      ManifoldSmoothFunctor.manifoldSmoothPullback E E A
        (fun x : X => (⟨x, by trivial⟩ : (⊤ : Opens X)))
        (contMDiff_manifoldTopLift E X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [manifoldSmoothPresheafTopIso, Iso.trans_hom, HomologicalComplex.comp_f,
    manifoldSmoothPresheafSectionsIso_hom_f, Category.id_comp]
  rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSections

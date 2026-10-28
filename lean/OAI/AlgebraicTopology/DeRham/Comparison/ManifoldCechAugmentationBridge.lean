import OAI.AlgebraicTopology.DeRham.Comparison.CechComplexAugmentation
import OAI.Analysis.DifferentialForms.Manifold.CechDeRham

/-! # Manifold Cech Augmentation Bridge -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ManifoldCechAugmentationBridge

noncomputable section

/-!
# The generic Čech augmentation is the actual manifold-form augmentation

Evaluation of the manifold de Rham presheaf complex gives its genuine
open-domain forms. At the top open set, the established global-section
identification intertwines the generic restriction augmentation with the
already verified actual manifold Čech augmentation. This discharges the
source-augmentation hypothesis in generic Čech descent.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

universe u

variable (E M : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Generic evaluation of the actual form presheaf complex gives the actual open de Rham complex. -/
def manifoldPresheafSectionsIso (W : Opens M) :
    CechComplexAugmentation.presheafComplexSections W (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E M) ≅
      Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex E W :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    obtain rfl := (show i + 1 = j from hij)
    rw [CechComplexAugmentation.presheafComplexSections_d, Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex_d,
      Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex_d]
    rfl)

/-- At the top open set, generic evaluation gives genuine global manifold forms. -/
def manifoldPresheafGlobalSectionsIso :
    CechComplexAugmentation.presheafComplexSections (⊤ : Opens M) (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E M) ≅
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M :=
  HomologicalComplex.Hom.isoOfComponents (fun n => Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormGlobalSectionsIso E M n) (by
    intro i j hij
    obtain rfl := (show i + 1 = j from hij)
    rw [CechComplexAugmentation.presheafComplexSections_d, Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex_d, Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro form
    exact Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal_d form)

@[simp]
theorem manifoldPresheafGlobalSectionsIso_hom_f_apply (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (⊤ : Opens M) n) :
    ((manifoldPresheafGlobalSectionsIso E M).hom.f n) form =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal form := rfl

@[simp]
theorem manifoldPresheafGlobalSectionsIso_inv_f_apply (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    ((manifoldPresheafGlobalSectionsIso E M).inv.f n) form =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ form := rfl

variable {ι : Type u} (U : ι → Opens M)

/-- Both total-complex presentations use exactly the same actual manifold Čech bicomplex. -/
def manifoldPresheafCechTotalIso :
    CechTotalFunctor.cechTotalComplex U (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E M) ≅
      Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) U := Iso.refl _

/-- The column augmentations agree under the genuine global-section identification. -/
theorem manifoldPresheafCechColumnAugmentation_eq :
    (manifoldPresheafGlobalSectionsIso E M).hom ≫ Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechColumnAugmentation (E := E) U =
      CechComplexAugmentation.cechColumnAugmentation U ⊤ (fun _ => le_top) (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E M) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  funext a
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  exact Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal_apply form x

/-- The generic total augmentation is the already constructed actual manifold augmentation. -/
theorem manifoldPresheafCechAugmentation_eq :
    (manifoldPresheafGlobalSectionsIso E M).hom ≫ Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := E) U =
      CechComplexAugmentation.cechTotalAugmentation U ⊤ (fun _ => le_top) (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E M) ≫
        (manifoldPresheafCechTotalIso E M U).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  let g := (manifoldPresheafGlobalSectionsIso E M).hom.f n
  let a := (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechColumnAugmentation (E := E) U).f n
  let b := (CechComplexAugmentation.cechColumnAugmentation U ⊤ (fun _ => le_top)
    (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E M)).f n
  let i := Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion (E := E) U 0 n n (Nat.zero_add n)
  have hc : g ≫ a = b := congrArg (fun f => f.f n)
    (manifoldPresheafCechColumnAugmentation_eq E M U)
  change g ≫ (a ≫ i) = (b ≫ i) ≫ 𝟙 _
  calc
    g ≫ (a ≫ i) = (g ≫ a) ≫ i := (Category.assoc _ _ _).symm
    _ = b ≫ i := congrArg (fun f => f ≫ i) hc
    _ = (b ≫ i) ≫ 𝟙 _ := (Category.comp_id _).symm

/-- The two actual augmentations are isomorphic as arrows of complexes. -/
def manifoldPresheafCechAugmentationArrowIso :
    Arrow.mk (CechComplexAugmentation.cechTotalAugmentation U ⊤ (fun _ => le_top)
      (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E M)) ≅
    Arrow.mk (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := E) U) :=
  Arrow.isoMk (manifoldPresheafGlobalSectionsIso E M) (manifoldPresheafCechTotalIso E M U)
    (manifoldPresheafCechAugmentation_eq E M U)

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]

/-- The generic source augmentation in Čech descent is a quasi-isomorphism,
using the fully proved actual manifold gluing and partition comparison. -/
theorem manifoldPresheafCechAugmentation_quasiIso (hcover : ∀ x : M, ∃ i, x ∈ U i) :
    QuasiIso (CechComplexAugmentation.cechTotalAugmentation U ⊤ (fun _ => le_top)
      (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E M)) :=
  (quasiIso_iff_of_arrow_mk_iso _ _ (manifoldPresheafCechAugmentationArrowIso E M U)).2
    (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal_quasiIso U hcover)

end

end OAI.AlgebraicTopology.DeRham.Comparison.ManifoldCechAugmentationBridge

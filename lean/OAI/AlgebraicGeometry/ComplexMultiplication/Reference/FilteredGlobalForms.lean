import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredSmoothMap
import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceCanonicalClosedForms
import OAI.AlgebraicGeometry.Comparison.Betti.GlobalFilteredSections

/-! # Filtered Global Forms -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredGlobalForms

noncomputable section

/-! # The original filtered global classes are classes of genuinely filtered closed forms -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Model" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "M" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X
local notation "Y" => TopCat.of M
local notation "Γ" => OAI.AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
local notation "ΓNat" => Functor.mapHomologicalComplex (Γ) (ComplexShape.up ℕ)
local notation "ΓInt" => Functor.mapHomologicalComplex (Γ) (ComplexShape.up ℤ)
local notation "FN" => Functor.mapHomologicalComplex
  (forget₂ (ModuleCat ℂ) AddCommGrpCat) (ComplexShape.up ℕ)
local notation "DR" => OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex Model M
local notation "G" => fun r => OAI.AlgebraicGeometry.Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt Y
  (FilteredSmoothInt.originalFilteredSmoothComplexInt X r)

/-- Actual filtered global sections map to their actual underlying manifold forms. -/
def originalFilteredGlobalToManifoldNat (r : ℤ) :=
  (ΓNat).map (FilteredSmoothAdditiveAcyclic.originalFilteredSmoothInclusionNat X r) ≫
    (ReferenceSmooth.GlobalForms.originalSmoothGlobalSectionsNatIso X).hom

/-- The same map in the literal original integer grading. -/
def originalFilteredGlobalToManifoldInt (r : ℤ) :
    (G) r ⟶ ReferenceSmooth.GlobalForms.originalManifoldDeRhamComplexInt X :=
  (ΓInt).map (FilteredSmoothInt.originalFilteredSmoothInclusionInt X r) ≫
    (ReferenceSmooth.GlobalForms.originalSmoothGlobalSectionsIntIso X).hom

set_option backward.isDefEq.respectTransparency false in
/-- Extension by zero retains the complete actual filtered global map. -/
theorem originalFilteredGlobalToManifoldInt_normalization (r : ℤ) :
    originalFilteredGlobalToManifoldInt X r =
      (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (Γ)
        (FilteredSmoothAdditiveAcyclic.originalFilteredSmoothComplexNat X r) ComplexShape.embeddingUpNat).hom ≫
          HomologicalComplex.extendMap (originalFilteredGlobalToManifoldNat X r)
            ComplexShape.embeddingUpNat := by
  have hn := Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_naturality (Γ)
    (FilteredSmoothAdditiveAcyclic.originalFilteredSmoothComplexNat X r) ComplexShape.embeddingUpNat
      (FilteredSmoothAdditiveAcyclic.originalFilteredSmoothInclusionNat X r)
  have hc := congrArg (fun g => g ≫ HomologicalComplex.extendMap
    (ReferenceSmooth.GlobalForms.originalSmoothGlobalSectionsNatIso X).hom ComplexShape.embeddingUpNat) hn
  simpa only [originalFilteredGlobalToManifoldInt,
    FilteredSmoothInt.originalFilteredSmoothInclusionInt, ReferenceSmooth.GlobalForms.originalSmoothGlobalSectionsIntIso,
    Iso.trans_hom, Functor.mapIso_hom, ComplexShape.Embedding.extendFunctor_map,
    Category.assoc, ← HomologicalComplex.extendMap_comp,
    originalFilteredGlobalToManifoldNat] using! hc

set_option backward.isDefEq.respectTransparency false in
/-- The retained component is the same actual filtered open form converted to a global form. -/
theorem originalFilteredGlobalToManifoldInt_retained_component (r : ℤ) (n : ℕ) :
    (originalFilteredGlobalToManifoldInt X r).f (n : ℤ) ≫
        (((FN).obj (DR)).extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom =
      (Γ).map ((FilteredSmoothAdditiveAcyclic.originalFilteredSmoothComplexNat X r).extendXIso
        ComplexShape.embeddingUpNat (i := n) rfl).hom ≫
          (originalFilteredGlobalToManifoldNat X r).f n := by
  have hm := Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_hom_f (Γ)
    (FilteredSmoothAdditiveAcyclic.originalFilteredSmoothComplexNat X r) ComplexShape.embeddingUpNat
      (i := n) (j := (n : ℤ)) rfl
  have hf := HomologicalComplex.extendMap_f (originalFilteredGlobalToManifoldNat X r)
    ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl
  rw [originalFilteredGlobalToManifoldInt_normalization, HomologicalComplex.comp_f, hm, hf]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- A cycle of the original filtered global complex gives an actual closed manifold form. -/
def originalFilteredGlobalCycleForm (r : ℤ) (n : ℕ) (c : ((G) r).cycles (n : ℤ)) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms Model M n :=
  (Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamClosedFormsIso Model M n).hom
    ((ReferenceCanonicalClosedForms.moduleIntegerAdditiveCyclesIso (DR) n).hom
      (HomologicalComplex.cyclesMap (originalFilteredGlobalToManifoldInt X r) (n : ℤ) c))

set_option backward.isDefEq.respectTransparency false in
/-- This closed form belongs to the genuine smooth Hodge filtration. -/
theorem originalFilteredGlobalCycleForm_filtered (r : ℤ) (n : ℕ)
    (c : ((G) r).cycles (n : ℤ)) :
    (originalFilteredGlobalCycleForm X r n c).val ∈
      Comparison.Betti.ManifoldFormFiltration.Hodge.manifoldFormFiltration Model M n r := by
  let s : Comparison.Betti.Open.FiltrationDescent.Hodge.openFormFiltration (E := Model) (⊤ : Opens M) n r :=
    (Γ).map ((FilteredSmoothAdditiveAcyclic.originalFilteredSmoothComplexNat X r).extendXIso
      ComplexShape.embeddingUpNat (i := n) rfl).hom (((G) r).iCycles (n : ℤ) c)
  have he : (originalFilteredGlobalCycleForm X r n c).val =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal s.val := by
    rw [originalFilteredGlobalCycleForm, Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldDeRhamClosedFormsIso_hom_coe]
    have hi := ConcreteCategory.congr_hom (ReferenceCanonicalClosedForms.moduleIntegerAdditiveCyclesIso_hom_i (DR) n)
      (HomologicalComplex.cyclesMap (originalFilteredGlobalToManifoldInt X r) (n : ℤ) c)
    have hc := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (originalFilteredGlobalToManifoldInt X r) (n : ℤ)) c
    have hn := ConcreteCategory.congr_hom
      (originalFilteredGlobalToManifoldInt_retained_component X r n)
        (((G) r).iCycles (n : ℤ) c)
    simp only [AddCommGrpCat.comp_apply] at hi hc hn
    exact hi.trans ((congrArg
      (((FN).obj (DR)).extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom hc).trans hn)
  rw [he]
  exact Comparison.Betti.GlobalFilteredSections.Hodge.toGlobal_mem_manifoldFormFiltration Model M n r s.val s.property

set_option backward.isDefEq.respectTransparency false in
/-- Taking the original class retains the class of this same actual closed form. -/
theorem originalFilteredGlobalCycleForm_class (r : ℤ) (n : ℕ)
    (c : ((G) r).cycles (n : ℤ)) :
    (CanonicalGlobalNormalization.originalManifoldIntegerDeRhamCohomologyIso X n).hom
      (HomologicalComplex.homologyMap (originalFilteredGlobalToManifoldInt X r) (n : ℤ)
        (((G) r).homologyπ (n : ℤ) c)) =
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass Model M n (originalFilteredGlobalCycleForm X r n c) := by
  let c' := HomologicalComplex.cyclesMap (originalFilteredGlobalToManifoldInt X r) (n : ℤ) c
  have hp := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (originalFilteredGlobalToManifoldInt X r) (n : ℤ)) c
  simp only [AddCommGrpCat.comp_apply] at hp
  rw [hp]
  have hi := ConcreteCategory.congr_hom (ReferenceCanonicalClosedForms.moduleIntegerAdditiveHomologyIso_π (DR) n) c'
  simp only [AddCommGrpCat.comp_apply] at hi
  have hn := ConcreteCategory.congr_hom
    (Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamClosedFormsIso_comp_class Model M n)
      ((ReferenceCanonicalClosedForms.moduleIntegerAdditiveCyclesIso (DR) n).hom c')
  simp only [ModuleCat.comp_apply] at hn
  exact hi.trans hn.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredGlobalForms

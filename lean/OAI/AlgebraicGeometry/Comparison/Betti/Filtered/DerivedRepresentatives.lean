import OAI.AlgebraicGeometry.Comparison.Betti.ExtendedAcyclicCocycles
import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.FormExtVanishing
import OAI.AlgebraicGeometry.Comparison.Betti.GlobalFilteredSections
import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.SmoothComplex

/-! # Derived Representatives -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Filtered.DerivedRepresentatives.Hodge

noncomputable section

/-! Filtered hypercohomology on a compact complex manifold is represented
by actual closed globally filtered forms with the original cocycle normalization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

abbrev filteredSheafTerm (n : ℕ) (r : ℤ) : ConstantSheafSections.ComplexSheaves (TopCat.of M) :=
  SmoothComplex.Hodge.filteredFormSheaf E M n r

abbrev filteredSheafComplexNat (r : ℤ) : CochainComplex (ConstantSheafSections.ComplexSheaves (TopCat.of M)) ℕ :=
  SmoothComplex.Hodge.filteredSmoothSheafComplex E M r

local instance : HasDerivedCategory.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := HasDerivedCategory.standard _
local instance : HasExt.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := HasExt.standard _

def filteredGlobalCocycle (n : ℕ) (r : ℤ) (a : ManifoldFormFiltration.Hodge.manifoldFormFiltration E M n r) :
    ConstantSheafSections.standardConstantSheaf (TopCat.of M) ⟶ (filteredSheafComplexNat E M r).X n :=
  (ConstantSheafSections.constantHomSectionsLinearEquiv (filteredSheafTerm E M n r)).symm
    ((GlobalFilteredSections.Hodge.globalFilteredSectionsEquiv E M n r).symm a)

theorem filteredGlobalCocycle_closed (n : ℕ) (r : ℤ) (a : ManifoldFormFiltration.Hodge.manifoldFormFiltration E M n r)
    (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a.val = 0) :
    filteredGlobalCocycle E M n r a ≫ (filteredSheafComplexNat E M r).d n (n + 1) = 0 := by
  apply (ConstantSheafSections.constantHomSectionsLinearEquiv (filteredSheafTerm E M (n + 1) r)).injective
  erw [ConstantSheafSections.constantHomSectionsLinearEquiv_naturality, map_zero]
  rw [SmoothComplex.Hodge.filteredSmoothSheafComplex_d]
  change SmoothComplex.Hodge.filteredOpenDifferential E M ⊤ n r
    ((ConstantSheafSections.constantHomSectionsLinearEquiv (filteredSheafTerm E M n r))
      ((ConstantSheafSections.constantHomSectionsLinearEquiv (filteredSheafTerm E M n r)).symm
        ((GlobalFilteredSections.Hodge.globalFilteredSectionsEquiv E M n r).symm a))) = 0
  erw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ a.val) = 0
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_d, ha, map_zero]

def filteredGlobalDerivedClass (n : ℕ) (r : ℤ) (a : ManifoldFormFiltration.Hodge.manifoldFormFiltration E M n r)
    (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a.val = 0) :
    (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves (TopCat.of M)) 0).obj
        (ConstantSheafSections.standardConstantSheaf (TopCat.of M)) ⟶
      (DerivedCategory.Q.obj ((filteredSheafComplexNat E M r).extend
        (ComplexShape.embeddingUpIntGE 0)))⟦(n : ℤ)⟧ :=
  ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom
    (ExtendedAcyclicCocycles.Ext.extendedCocycle _ _ n (filteredGlobalCocycle E M n r a))
    (ExtendedAcyclicCocycles.Ext.extendedCocycle_closed _ _ n (filteredGlobalCocycle E M n r a)
      (filteredGlobalCocycle_closed E M n r a ha))) DerivedCategory.Q

variable [CompactSpace M] [T2Space M]

theorem exists_filtered_global_derived_representative (n : ℕ) (r : ℤ)
    (a : (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves (TopCat.of M)) 0).obj
        (ConstantSheafSections.standardConstantSheaf (TopCat.of M)) ⟶
      (DerivedCategory.Q.obj ((filteredSheafComplexNat E M r).extend
        (ComplexShape.embeddingUpIntGE 0)))⟦(n : ℤ)⟧) :
    ∃ (b : ManifoldFormFiltration.Hodge.manifoldFormFiltration E M n r) (hb : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b.val = 0),
      filteredGlobalDerivedClass E M n r b hb = a := by
  let K : CochainComplex (ConstantSheafSections.ComplexSheaves (TopCat.of M)) ℕ := filteredSheafComplexNat E M r
  let A := ConstantSheafSections.standardConstantSheaf (TopCat.of M)
  have hExt : ∀ p q, Subsingleton (Ext.{1} A (K.X p) (q + 1)) :=
    fun p q => FormExtVanishing.Hodge.filteredFormSheaf_ext_vanish E M p r q
  obtain ⟨f, hf, hfa⟩ := ExtendedAcyclicCocycles.Ext.exists_nonnegative_derived_cocycle A K hExt n a
  let s : Open.FiltrationDescent.Hodge.openFormFiltration (E := E) (⊤ : Opens M) n r :=
    ConstantSheafSections.constantHomSectionsLinearEquiv (filteredSheafTerm E M n r) f
  have hs : SmoothComplex.Hodge.filteredOpenDifferential E M ⊤ n r s = 0 := by
    have h := congrArg (ConstantSheafSections.constantHomSectionsLinearEquiv (filteredSheafTerm E M (n + 1) r)) hf
    erw [ConstantSheafSections.constantHomSectionsLinearEquiv_naturality, map_zero] at h
    change (K.d n (n + 1)).hom.app (op ⊤) s = 0 at h
    change ((filteredSheafComplexNat E M r).d n (n + 1)).hom.app (op ⊤) s = 0 at h
    rw [SmoothComplex.Hodge.filteredSmoothSheafComplex_d] at h
    exact h
  let b := GlobalFilteredSections.Hodge.globalFilteredSectionsEquiv E M n r s
  have hb : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b.val = 0 := by
    change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal s.val) = 0
    have hd : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d s.val = 0 := congrArg Subtype.val hs
    rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal_d, hd, map_zero]
  have hbf : filteredGlobalCocycle E M n r b = f := by
    change (ConstantSheafSections.constantHomSectionsLinearEquiv (filteredSheafTerm E M n r)).symm
      ((GlobalFilteredSections.Hodge.globalFilteredSectionsEquiv E M n r).symm ((GlobalFilteredSections.Hodge.globalFilteredSectionsEquiv E M n r) s)) = f
    rw [LinearEquiv.symm_apply_apply]
    exact LinearEquiv.symm_apply_apply _ f
  refine ⟨b, hb, ?_⟩
  unfold filteredGlobalDerivedClass
  simp only [hbf]
  convert hfa using 1

end

end OAI.AlgebraicGeometry.Comparison.Betti.Filtered.DerivedRepresentatives.Hodge

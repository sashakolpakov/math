import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.DerivedRepresentatives
import OAI.AlgebraicGeometry.Comparison.Betti.NonnegativeCocycleNaturality

/-! # Derived Inclusion -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Filtered.DerivedInclusion.Hodge

noncomputable section

/-! Including a closed filtered form into the actual smooth complex gives
exactly its original smooth derived cocycle class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

abbrev smoothSheafTerm (n : ℕ) : ConstantSheafSections.ComplexSheaves (TopCat.of M) := Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n

abbrev smoothSheafComplexNat : CochainComplex (ConstantSheafSections.ComplexSheaves (TopCat.of M)) ℕ :=
  Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M

local instance : HasDerivedCategory.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := HasDerivedCategory.standard _

def smoothGlobalCocycle (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    ConstantSheafSections.standardConstantSheaf (TopCat.of M) ⟶ (smoothSheafComplexNat E M).X n :=
  (ConstantSheafSections.constantHomSectionsLinearEquiv (smoothSheafTerm E M n)).symm (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ a)

omit [FiniteDimensional ℝ E] in
theorem smoothGlobalCocycle_closed (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0) :
    smoothGlobalCocycle E M n a ≫ (smoothSheafComplexNat E M).d n (n + 1) = 0 := by
  apply (ConstantSheafSections.constantHomSectionsLinearEquiv (smoothSheafTerm E M (n + 1))).injective
  erw [ConstantSheafSections.constantHomSectionsLinearEquiv_naturality, map_zero]
  rw [Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex_d]
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d
    ((ConstantSheafSections.constantHomSectionsLinearEquiv (smoothSheafTerm E M n))
      ((ConstantSheafSections.constantHomSectionsLinearEquiv (smoothSheafTerm E M n)).symm
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ a))) = 0
  erw [LinearEquiv.apply_symm_apply]
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_d, ha, map_zero]

def smoothGlobalDerivedClass (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0) :
    (DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves (TopCat.of M)) 0).obj
        (ConstantSheafSections.standardConstantSheaf (TopCat.of M)) ⟶
      (DerivedCategory.Q.obj ((smoothSheafComplexNat E M).extend
        (ComplexShape.embeddingUpIntGE 0)))⟦(n : ℤ)⟧ :=
  ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom
    (ExtendedAcyclicCocycles.Ext.extendedCocycle _ _ n (smoothGlobalCocycle E M n a))
    (ExtendedAcyclicCocycles.Ext.extendedCocycle_closed _ _ n (smoothGlobalCocycle E M n a)
      (smoothGlobalCocycle_closed E M n a ha))) DerivedCategory.Q

theorem filteredGlobalCocycle_inclusion (n : ℕ) (r : ℤ) (a : ManifoldFormFiltration.Hodge.manifoldFormFiltration E M n r) :
    DerivedRepresentatives.Hodge.filteredGlobalCocycle E M n r a ≫ (SmoothComplex.Hodge.filteredSmoothSheafInclusion E M r).f n =
      smoothGlobalCocycle E M n a.val := by
  apply (ConstantSheafSections.constantHomSectionsLinearEquiv (smoothSheafTerm E M n)).injective
  erw [ConstantSheafSections.constantHomSectionsLinearEquiv_naturality]
  dsimp only [DerivedRepresentatives.Hodge.filteredGlobalCocycle, smoothGlobalCocycle]
  erw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem filteredGlobalDerivedClass_inclusion (n : ℕ) (r : ℤ) (a : ManifoldFormFiltration.Hodge.manifoldFormFiltration E M n r)
    (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a.val = 0) :
    DerivedRepresentatives.Hodge.filteredGlobalDerivedClass E M n r a ha ≫
      (DerivedCategory.Q.map (HomologicalComplex.extendMap (SmoothComplex.Hodge.filteredSmoothSheafInclusion E M r)
        (ComplexShape.embeddingUpIntGE 0)))⟦(n : ℤ)⟧' = smoothGlobalDerivedClass E M n a.val ha := by
  have h := NonnegativeCocycleNaturality.Ext.derivedExtendedCocycle_postcomp n (DerivedRepresentatives.Hodge.filteredGlobalCocycle E M n r a)
    (DerivedRepresentatives.Hodge.filteredGlobalCocycle_closed E M n r a ha) (SmoothComplex.Hodge.filteredSmoothSheafInclusion E M r)
  simp only [filteredGlobalCocycle_inclusion] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Filtered.DerivedInclusion.Hodge

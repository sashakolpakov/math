import OAI.AlgebraicGeometry.Comparison.Betti.Open.FiltrationDescent
import OAI.Analysis.DifferentialForms.Manifold.SheafDeRham

/-! # Smooth Complex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Filtered.SmoothComplex.Hodge

noncomputable section

section

/-! Sheaves of actual filtered smooth forms, with their literal inclusion
into the original manifold form sheaves. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

instance filteredOpenAddCommGroup (U : Opens M) (n : ℕ) (r : ℤ) :
    AddCommGroup (Open.FiltrationDescent.Hodge.openFormFiltration (E := E) U n r) :=
  @Submodule.addCommGroup ℂ (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) inferInstance inferInstance
    inferInstance (Open.FiltrationDescent.Hodge.openFormFiltration (E := E) U n r)

def filteredOpenRestriction {U V : Opens M} (h : V ≤ U) (n : ℕ) (r : ℤ) :
    Open.FiltrationDescent.Hodge.openFormFiltration (E := E) U n r →ₗ[ℂ] Open.FiltrationDescent.Hodge.openFormFiltration (E := E) V n r where
  toFun a := ⟨Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a.val, Open.FiltrationDescent.Hodge.openFormFiltration_restrict h n r a.val a.property⟩
  map_add' a b := Subtype.ext ((Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h).map_add a.val b.val)
  map_smul' c a := Subtype.ext ((Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h).map_smul c a.val)

def filteredFormPresheaf (n : ℕ) (r : ℤ) :
    (Opens M)ᵒᵖ ⥤ ModuleCat.{0} ℂ where
  obj U := ModuleCat.of ℂ (Open.FiltrationDescent.Hodge.openFormFiltration (E := E) (M := M) U.unop n r)
  map f := ModuleCat.ofHom (filteredOpenRestriction E M (leOfHom f.unop) n r)
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact Subtype.ext (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_refl a.val)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro x
    rfl

theorem filteredFormPresheaf_isSheaf [FiniteDimensional ℝ E] (n : ℕ) (r : ℤ) :
    TopCat.Presheaf.IsSheaf (X := TopCat.of M) (filteredFormPresheaf E M n r) := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := TopCat.of M)
    (filteredFormPresheaf E M n r)).mpr
  intro ι U a ha
  have hcompat : ∀ i j,
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (show U i ⊓ U j ≤ U i from inf_le_left) (a i).val =
        Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (show U i ⊓ U j ≤ U j from inf_le_right) (a j).val :=
    fun i j => congrArg Subtype.val (ha i j)
  obtain ⟨b, hb, huniq⟩ := Open.FiltrationDescent.Hodge.existsUnique_filteredForm_glue U n r a hcompat
  refine ⟨b, fun i => Subtype.ext (hb i), ?_⟩
  intro c hc
  exact huniq c (fun i => congrArg Subtype.val (hc i))

def filteredFormSheaf [FiniteDimensional ℝ E] (n : ℕ) (r : ℤ) :
    TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M) :=
  ⟨filteredFormPresheaf E M n r, filteredFormPresheaf_isSheaf E M n r⟩

def filteredFormPresheafInclusion (n : ℕ) (r : ℤ) :
    filteredFormPresheaf E M n r ⟶ Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf E M n where
  app U := ModuleCat.ofHom (Open.FiltrationDescent.Hodge.openFormFiltration (E := E) U.unop n r).subtype
  naturality {U V} f := by rfl

def filteredFormSheafInclusion [FiniteDimensional ℝ E] (n : ℕ) (r : ℤ) :
    filteredFormSheaf E M n r ⟶ Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n :=
  ObjectProperty.homMk (filteredFormPresheafInclusion E M n r)

end

/-! The genuine filtered smooth de Rham sheaf complex and its original
exterior differential and inclusion. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

def filteredOpenDifferential (U : Opens M) (n : ℕ) (r : ℤ) :
    Open.FiltrationDescent.Hodge.openFormFiltration (E := E) U n r →ₗ[ℂ] Open.FiltrationDescent.Hodge.openFormFiltration (E := E) U (n + 1) r where
  toFun a := ⟨Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a.val, Open.FiltrationDescent.Hodge.openFormFiltration_d n r a.val a.property⟩
  map_add' a b := Subtype.ext (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d.map_add a.val b.val)
  map_smul' c a := Subtype.ext (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d.map_smul c a.val)

def filteredFormPresheafD (n : ℕ) (r : ℤ) :
    filteredFormPresheaf E M n r ⟶ filteredFormPresheaf E M (n + 1) r where
  app U := ModuleCat.ofHom (filteredOpenDifferential E M U.unop n r)
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact Subtype.ext ((Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_d (leOfHom f.unop) a.val).symm)

theorem filteredFormPresheafD_squared (n : ℕ) (r : ℤ) :
    filteredFormPresheafD E M n r ≫ filteredFormPresheafD E M (n + 1) r = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact Subtype.ext (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_squared a.val)

variable [FiniteDimensional ℝ E]

def filteredFormSheafD (n : ℕ) (r : ℤ) :
    filteredFormSheaf E M n r ⟶ filteredFormSheaf E M (n + 1) r :=
  ObjectProperty.homMk (filteredFormPresheafD E M n r)

theorem filteredFormSheafD_squared (n : ℕ) (r : ℤ) :
    filteredFormSheafD E M n r ≫ filteredFormSheafD E M (n + 1) r = 0 :=
  Sheaf.hom_ext (filteredFormPresheafD_squared E M n r)

def filteredSmoothSheafComplex (r : ℤ) :
    CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M)) ℕ :=
  CochainComplex.of (fun n => filteredFormSheaf E M n r)
    (fun n => filteredFormSheafD E M n r) (fun n => filteredFormSheafD_squared E M n r)

theorem filteredSmoothSheafComplex_d (r : ℤ) (n : ℕ) :
    (filteredSmoothSheafComplex E M r).d n (n + 1) = filteredFormSheafD E M n r :=
  CochainComplex.of_d (fun k => filteredFormSheaf E M k r)
    (fun k => filteredFormSheafD E M k r) n

def filteredSmoothSheafInclusion (r : ℤ) :
    filteredSmoothSheafComplex E M r ⟶ Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M where
  f n := filteredFormSheafInclusion E M n r
  comm' n m hnm := by
    obtain rfl := (show n + 1 = m from hnm)
    rw [filteredSmoothSheafComplex_d, Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex_d]
    rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Filtered.SmoothComplex.Hodge

import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.ScalarKoszul
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ProjectiveResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Koszul Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulResolution

noncomputable section

/-! The exterior Koszul complex as a projective resolution with its literal
augmentation to the original quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.GeneratorMatrix OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology
  AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction

universe u
variable (R : Type u) [CommRing R] {n : ℕ} (s : Fin n → R)

theorem equation_range : (Koszul.GeneratorMatrix.equation R s).range = Koszul.OrientedTopCohomology.ideal R s := by
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    rw [Koszul.GeneratorMatrix.equation_apply]
    apply Submodule.sum_mem
    intro i _
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self i))
  · apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    simp [Koszul.GeneratorMatrix.equation_apply, Pi.single_apply]

theorem contraction_zero (x : ⋀[R]^1 (Fin n → R)) :
    exteriorPower.zeroEquiv R _ (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Koszul.GeneratorMatrix.equation R s) 0 x) =
      Koszul.GeneratorMatrix.equation R s (exteriorPower.oneEquiv R _ x) := by
  have he : (exteriorPower.zeroEquiv R _).toLinearMap.comp (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Koszul.GeneratorMatrix.equation R s) 0) =
      (Koszul.GeneratorMatrix.equation R s).comp (exteriorPower.oneEquiv R _).toLinearMap := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span R 1 (Fin n → R))
    rintro _ ⟨v, rfl⟩
    let z : Fin 0 → (Fin n → R) := fun i => Fin.elim0 i
    have hv : v = Fin.cons (v 0) z := by ext i; fin_cases i; rfl
    change exteriorPower.zeroEquiv R _
      (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Koszul.GeneratorMatrix.equation R s) 0 (exteriorPower.ιMulti R 1 v)) = _
    rw [hv, ← AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge_ιMulti, AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction_wedge_zero, map_smul,
      exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge_ιMulti]
    exact (congrArg (Koszul.GeneratorMatrix.equation R s)
      (exteriorPower.oneEquiv_ιMulti (R := R) (Fin.cons (v 0) z))).symm
  exact LinearMap.congr_fun he x

def augmentationZero : (Koszul.OrientedTopCohomology.koszul R s).X 0 ⟶ ModuleCat.of R (R ⧸ Koszul.OrientedTopCohomology.ideal R s) :=
  ModuleCat.ofHom ((Koszul.OrientedTopCohomology.ideal R s).mkQ.comp (exteriorPower.zeroEquiv R _).toLinearMap)

theorem augmentationZero_condition : (Koszul.OrientedTopCohomology.koszul R s).d 1 0 ≫ augmentationZero R s = 0 := by
  rw [KoszulHomotopy.complex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (Koszul.OrientedTopCohomology.ideal R s).mkQ (exteriorPower.zeroEquiv R _
    (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R _ (Koszul.GeneratorMatrix.equation R s) 0 x)) = 0
  rw [contraction_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [← equation_range]
  exact LinearMap.mem_range_self _ _

theorem augmentationZero_exact :
    (ShortComplex.mk _ _ (augmentationZero_condition R s)).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  have hx' : exteriorPower.zeroEquiv R _ x ∈ Koszul.OrientedTopCohomology.ideal R s :=
    (Submodule.Quotient.mk_eq_zero _).mp hx
  rw [← equation_range] at hx'
  obtain ⟨v, hv⟩ := hx'
  refine ⟨(exteriorPower.oneEquiv R _).symm v, ?_⟩
  change (Koszul.OrientedTopCohomology.koszul R s).d 1 0 _ = x
  rw [KoszulHomotopy.complex_d]
  apply (exteriorPower.zeroEquiv R _).injective
  erw [contraction_zero, LinearEquiv.apply_symm_apply]
  exact hv

instance augmentationZero_epi : Epi (augmentationZero R s) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  exact (Submodule.mkQ_surjective _).comp (exteriorPower.zeroEquiv R _).surjective

theorem term_free (m : ℕ) : Module.Free R ((Koszul.OrientedTopCohomology.koszul R s).X m) := by
  let e := ScalarKoszul.Comparison.iso R s
  let f := (Koszul.OrientedTopCohomology.koszul R s).extendXIso ScalarKoszul.Comparison.shape (i := m) rfl
  let g := (HomologicalComplex.eval _ _ (ScalarKoszul.Comparison.shape.f m)).mapIso e
  let : Module.Free R
      ↑((HomologicalComplex.eval (ModuleCat R) (.up ℤ) (ScalarKoszul.Comparison.shape.f m)).obj
        (RegularSequenceKoszul.complex (ModuleCat.of R R) (List.ofFn s))) :=
    RegularSequenceKoszul.term_free (ModuleCat.of R R) (List.ofFn s)
      (ScalarKoszul.Comparison.shape.f m)
  exact Module.Free.of_equiv (g.symm ≪≫ f).toLinearEquiv

instance term_projective (m : ℕ) : Projective ((Koszul.OrientedTopCohomology.koszul R s).X m) := by
  let := term_free R s m
  infer_instance

theorem exactAt_succ (hs : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s)) (m : ℕ) :
    (Koszul.OrientedTopCohomology.koszul R s).ExactAt (m + 1) := by
  obtain ⟨ε, hε⟩ := ScalarKoszul.Comparison.exists_augmentation R s hs
  let := hε
  apply ((Koszul.OrientedTopCohomology.koszul R s).extend_exactAt_iff ScalarKoszul.Comparison.shape
    (j := m + 1) rfl).mp
  apply (exactAt_iff_of_quasiIsoAt ε _).mpr
  exact exactAt_single_obj _ _ _ _ (by
    change 0 - ((m + 1 : ℕ) : ℤ) ≠ 0
    omega)

def resolution (hs : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s)) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Koszul.OrientedTopCohomology.ideal R s)) :=
  Augmented.ProjectiveResolution.resolution (Koszul.OrientedTopCohomology.koszul R s) _ (augmentationZero R s)
    (augmentationZero_condition R s) (exactAt_succ R s hs) (augmentationZero_exact R s)

@[simp] theorem resolution_π_f_zero (hs : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s)) :
    (resolution R s hs).π.f 0 = augmentationZero R s :=
  Augmented.ProjectiveResolution.resolution_π_f_zero _ _ _ _ _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulResolution

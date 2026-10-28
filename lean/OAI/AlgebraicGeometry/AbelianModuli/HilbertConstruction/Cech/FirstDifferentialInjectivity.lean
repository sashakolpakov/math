import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.DegreeZeroLinearity
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # First Differential Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.FirstDifferentialInjectivity

noncomputable section

/-! Vanishing global sections makes the first coefficient Cech differential injective. Tensoring on the right by a flat module preserves this actual differential's injectivity. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

variable {R : Type u} [CommRing R]

theorem moduleCochain_firstDifferential_injective
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (hC : C.ExactAt 0) :
    Function.Injective (C.d 0 1) := by
  have hs : (C.sc' 0 0 1).Exact :=
    (C.exactAt_iff' 0 0 1 (by simp) (by simp)).mp hC
  have hzero : C.d 0 0 = 0 := C.shape 0 0 (by simp)
  intro x y hxy
  have hsub : C.d 0 1 (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := ((C.sc' 0 0 1).moduleCat_exact_iff.mp hs) (x - y) hsub
  change C.d 0 0 z = x - y at hz
  apply sub_eq_zero.mp
  calc
    x - y = C.d 0 0 z := hz.symm
    _ = 0 := by rw [hzero]; rfl

theorem coefficientCech_firstDifferential_injective_of_sections_zero
    {X : Scheme.{u}} (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hM : Subsingleton Γ(M, ⊤)) :
    Function.Injective ((Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U).d 0 1) := by
  let : Subsingleton ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M) := hM
  have hz : IsZero ((Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U).homology 0) :=
    (CoefficientCech.DegreeZeroLinearity.coefficientCechZeroSectionsModuleIso c M U hU).isZero_iff.mp
      (ModuleCat.isZero_of_subsingleton _)
  exact moduleCochain_firstDifferential_injective (Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U)
    (((Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U).exactAt_iff_isZero_homology 0).mpr hz)

theorem coefficientCech_tensorRight_firstDifferential_injective
    {X : Scheme.{u}} (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hM : Subsingleton Γ(M, ⊤)) (V : ModuleCat.{u} R) [Module.Flat R V] :
    Function.Injective ((tensorRight V ⋙ HilbertConstruction.Module.ProductForget.moduleForget R).map
      ((Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U).d 0 1)) := by
  have : Mono ((Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U).d 0 1) :=
    (ModuleCat.mono_iff_injective _).mpr
      (coefficientCech_firstDifferential_injective_of_sections_zero c M U hU hM)
  have : Mono ((tensorRight V ⋙ HilbertConstruction.Module.ProductForget.moduleForget R).map
      ((Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U).d 0 1)) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).mp this

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.FirstDifferentialInjectivity

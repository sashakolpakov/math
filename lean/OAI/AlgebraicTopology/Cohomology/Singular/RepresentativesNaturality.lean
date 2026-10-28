import OAI.AlgebraicTopology.Cohomology.Singular.Representatives
import OAI.AlgebraicTopology.Cohomology.Singular.Functor

/-! # Representatives Naturality -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

noncomputable section

/-!
# Naturality of cocycle representatives

Cochain maps carry cocycles and coboundaries to cocycles and coboundaries.
The resulting representative map is compatible with mathlib's categorical
homology map. We specialize this to the genuine singular pullback and
coefficient maps, without defining another cohomology theory.
-/

open _root_.CategoryTheory

variable {R : Type} [Ring R]
variable {K L T : CochainComplex (ModuleCat.{0} R) ℕ}

/-- Restriction of a cochain map to the kernel of the outgoing differential. -/
def cochainCocycleMap (f : K ⟶ L) (n : ℕ) :
    Representatives.cochainCocycles K n →ₗ[R] Representatives.cochainCocycles L n :=
  ((f.f n).hom.comp (Representatives.cochainCocycles K n).subtype).codRestrict _ fun x => by
    rw [Representatives.mem_cochainCocycles_iff]
    change (L.d n (n + 1)) ((f.f n) (x : K.X n)) = 0
    have h := ConcreteCategory.congr_hom (f.comm n (n + 1)) (x : K.X n)
    have hx := (Representatives.mem_cochainCocycles_iff K n (x : K.X n)).mp x.property
    simpa only [ConcreteCategory.comp_apply, hx, map_zero] using h

@[simp]
theorem cochainCocycleMap_val (f : K ⟶ L) (n : ℕ) (x : Representatives.cochainCocycles K n) :
    (cochainCocycleMap f n x : L.X n) = (f.f n) (x : K.X n) := rfl

@[simp]
theorem cochainCocycleMap_id (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    cochainCocycleMap (𝟙 K) n = LinearMap.id := by
  ext x
  rfl

@[simp]
theorem cochainCocycleMap_comp (f : K ⟶ L) (g : L ⟶ T) (n : ℕ) :
    cochainCocycleMap (f ≫ g) n = (cochainCocycleMap g n).comp (cochainCocycleMap f n) := by
  ext x
  rfl

/-- The concrete cocycle map agrees with the categorical map on cycles. -/
theorem cochainCocycleMap_eq_cyclesMap (f : K ⟶ L) (n : ℕ)
    (x : Representatives.cochainCocycles K n) :
    (L.sc n).moduleCatCyclesIso.inv (cochainCocycleMap f n x) =
      (HomologicalComplex.cyclesMap f n) ((K.sc n).moduleCatCyclesIso.inv x) := by
  apply (ModuleCat.mono_iff_injective (L.iCycles n)).mp inferInstance
  have hL := ConcreteCategory.congr_hom ((L.sc n).moduleCatCyclesIso_inv_iCycles)
    (cochainCocycleMap f n x)
  have hK := ConcreteCategory.congr_hom ((K.sc n).moduleCatCyclesIso_inv_iCycles) x
  have hf := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f n)
    ((K.sc n).moduleCatCyclesIso.inv x)
  change (L.iCycles n) ((L.sc n).moduleCatCyclesIso.inv (cochainCocycleMap f n x)) =
    (L.iCycles n) ((HomologicalComplex.cyclesMap f n) ((K.sc n).moduleCatCyclesIso.inv x))
  change (L.iCycles n) ((L.sc n).moduleCatCyclesIso.inv (cochainCocycleMap f n x)) =
    (f.f n) (x : K.X n) at hL
  change (K.iCycles n) ((K.sc n).moduleCatCyclesIso.inv x) = (x : K.X n) at hK
  change (L.iCycles n) ((HomologicalComplex.cyclesMap f n)
    ((K.sc n).moduleCatCyclesIso.inv x)) =
      (f.f n) ((K.iCycles n) ((K.sc n).moduleCatCyclesIso.inv x)) at hf
  rw [hK] at hf
  exact hL.trans hf.symm

/-- Passing to a cohomology class commutes with every cochain map. -/
theorem cochainClass_naturality (f : K ⟶ L) (n : ℕ) (x : Representatives.cochainCocycles K n) :
    (HomologicalComplex.homologyMap f n) (Representatives.cochainClass K n x) =
      Representatives.cochainClass L n (cochainCocycleMap f n x) := by
  rw [Representatives.cochainClass_eq_homologyπ, Representatives.cochainClass_eq_homologyπ,
    cochainCocycleMap_eq_cyclesMap]
  exact ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f n)
    ((K.sc n).moduleCatCyclesIso.inv x)

/-- A cochain map carries the coboundary of a cochain to the coboundary of its image. -/
theorem cochainCocycleMap_boundary (f : K ⟶ L) (n : ℕ) (x : (K.sc n).X₁) :
    cochainCocycleMap f n (Representatives.cochainBoundaryMap K n x) =
      Representatives.cochainBoundaryMap L n ((f.f ((ComplexShape.up ℕ).prev n)) x) := by
  apply Subtype.ext
  exact (ConcreteCategory.congr_hom
    (f.comm ((ComplexShape.up ℕ).prev n) n) x).symm

/-- Pullback on singular cocycle representatives. -/
abbrev singularCocyclePullback (M : ModuleCat.{0} R) {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) : Representatives.singularCocycles M Y n →ₗ[R] Representatives.singularCocycles M X n :=
  cochainCocycleMap (Functor.singularPullback M f) n

/-- A pulled-back class is represented by the pulled-back cocycle. -/
theorem singularCohomologyPullback_class (M : ModuleCat.{0} R) {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (x : Representatives.singularCocycles M Y n) :
    (Functor.singularCohomologyPullback M f n) (Representatives.singularClass M Y n x) =
      Representatives.singularClass M X n (singularCocyclePullback M f n x) :=
  cochainClass_naturality (Functor.singularPullback M f) n x

/-- A coefficient map on singular cocycle representatives. -/
abbrev coefficientCocycleMap {M N : ModuleCat.{0} R} (f : M ⟶ N)
    (X : TopCat.{0}) (n : ℕ) : Representatives.singularCocycles M X n →ₗ[R] Representatives.singularCocycles N X n :=
  cochainCocycleMap (Coefficients.coefficientCochainMap f X) n

/-- Changing coefficients of a class changes coefficients of its representative. -/
theorem coefficientMap_class {M N : ModuleCat.{0} R} (f : M ⟶ N)
    (X : TopCat.{0}) (n : ℕ) (x : Representatives.singularCocycles M X n) :
    (Coefficients.coefficientMap f X n) (Representatives.singularClass M X n x) =
      Representatives.singularClass N X n (coefficientCocycleMap f X n x) :=
  cochainClass_naturality (Coefficients.coefficientCochainMap f X) n x

end

end OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

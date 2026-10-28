import OAI.AlgebraicGeometry.Divisors.LineBundles.EquationPeriodicComplex
import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.PeriodicComplex
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Factor Kill -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FactorKill.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: the actual cone for composition of scalar factors

For abc annihilating M, the cone compares the complexes (a,bc),
(ab,c), and (b,ac). Its two differentials are explicit two by two
matrices on M × M; their composites vanish by the given annihilation.
-/

open _root_.CategoryTheory

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def factorConeFirst (a b c : R) : (M × M) →ₗ[R] M × M :=
  ((a * b) • LinearMap.fst R M M + b • LinearMap.snd R M M).prod
    ((-(b * c)) • LinearMap.snd R M M)

def factorConeSecond (a c : R) : (M × M) →ₗ[R] M × M :=
  (c • LinearMap.fst R M M + LinearMap.snd R M M).prod
    ((-a) • LinearMap.snd R M M)

theorem factorCone_comp_zero (a b c : R) (h : ∀ m : M, (a * b * c) • m = 0) :
    (factorConeSecond a c).comp (factorConeFirst (M := M) a b c) = 0 := by
  apply LinearMap.ext
  intro m
  apply Prod.ext
  · change c • ((a * b) • m.1 + b • m.2) + (-(b * c)) • m.2 = 0
    calc
      _ = (a * b * c) • m.1 := by module
      _ = 0 := h m.1
  · change (-a) • ((-(b * c)) • m.2) = 0
    calc
      _ = (a * b * c) • m.2 := by module
      _ = 0 := h m.2

theorem factorCone_comp_zero_reverse (a b c : R) (h : ∀ m : M, (a * b * c) • m = 0) :
    (factorConeFirst a b c).comp (factorConeSecond (M := M) a c) = 0 := by
  apply LinearMap.ext
  intro m
  apply Prod.ext
  · change (a * b) • (c • m.1 + m.2) + b • ((-a) • m.2) = 0
    calc
      _ = (a * b * c) • m.1 := by module
      _ = 0 := h m.1
  · change (-(b * c)) • ((-a) • m.2) = 0
    calc
      _ = (a * b * c) • m.2 := by module
      _ = 0 := h m.2

def periodicFactorCone (a b c : R) (h : ∀ m : M, (a * b * c) • m = 0) :
    HomologicalComplex (ModuleCat R) PeriodicComplex.BundleCycles.periodicComplexShape :=
  PeriodicComplex.BundleCycles.endomorphismPeriodicComplex (factorConeFirst (M := M) a b c) (factorConeSecond (M := M) a c)
    (factorCone_comp_zero a b c h) (factorCone_comp_zero_reverse a b c h)

theorem factorCone_kill_middle (a b c : R) (h : ∀ m : M, (a * b * c) • m = 0) :
    ∀ m : M, (b * (a * c)) • m = 0 := by
  intro m
  rw [show b * (a * c) = a * b * c by ring]
  exact h m

theorem factorCone_kill_source (a b c : R) (h : ∀ m : M, (a * b * c) • m = 0) :
    ∀ m : M, (a * (b * c)) • m = 0 := by
  simpa only [mul_assoc] using h

end

section

/-!
# LineBundleCycles: explicit retraction of the factor cone

Projection sends (y,z) to ay+z in degree zero and (u,v) to u in degree
one. The section sends z to (0,z) and u to (u,-cu). These are actual
chain maps, and their composite on the scalar complex is the identity.
-/

open _root_.CategoryTheory

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a b c : R) (h : ∀ m : M, (a * b * c) • m = 0)

def factorConeProjection : periodicFactorCone a b c h ⟶
    EquationPeriodicComplex.BundleCycles.equationPeriodicComplex b (a * c) (factorCone_kill_middle a b c h) where
  f i := match i with
    | false => ModuleCat.ofHom (a • LinearMap.fst R M M + LinearMap.snd R M M)
    | true => ModuleCat.ofHom (LinearMap.fst R M M)
  comm' := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      change b • (a • m.1 + m.2) = (a * b) • m.1 + b • m.2
      module
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      change (a * c) • m.1 = a • (c • m.1 + m.2) + (-a) • m.2
      module
    · exact (hij rfl).elim

def factorConeSection : EquationPeriodicComplex.BundleCycles.equationPeriodicComplex b (a * c) (factorCone_kill_middle a b c h) ⟶
    periodicFactorCone a b c h where
  f i := match i with
    | false => ModuleCat.ofHom (LinearMap.inr R M M)
    | true => ModuleCat.ofHom ((LinearMap.id : M →ₗ[R] M).prod ((-c) • LinearMap.id))
  comm' := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      change M at m
      apply Prod.ext
      · change (a * b) • (0 : M) + b • m = b • m
        module
      · change (-(b * c)) • m = (-c) • (b • m)
        module
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      change M at m
      apply Prod.ext
      · change c • m + (-c) • m = 0
        module
      · change (-a) • ((-c) • m) = (a * c) • m
        module
    · exact (hij rfl).elim

theorem factorCone_section_projection :
    factorConeSection a b c h ≫ factorConeProjection a b c h = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change M at m
    change a • (0 : M) + m = m
    module
  · rfl

end

/-!
# LineBundleCycles: contraction of the extra summand in the factor cone

The homotopy sends (y,z) in degree zero to (0,y) in degree one.
It proves that the explicit section and projection are inverse on
homology, without assuming any homology comparison.
-/

open _root_.CategoryTheory

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a b c : R) (h : ∀ m : M, (a * b * c) • m = 0)

def factorConeContraction : Homotopy (𝟙 (periodicFactorCone a b c h))
    (factorConeProjection a b c h ≫ factorConeSection a b c h) where
  hom i j := match i, j with
    | false, true => ModuleCat.ofHom ((0 : (M × M) →ₗ[R] M).prod (LinearMap.fst R M M))
    | _, _ => 0
  zero := by
    intro i j hij
    cases i <;> cases j
    · rfl
    · exact (hij PeriodicComplex.BundleCycles.periodicComplexShape_true_false).elim
    · rfl
    · rfl
  comm := by
    intro i
    cases i
    · rw [dNext_eq _ PeriodicComplex.BundleCycles.periodicComplexShape_false_true, prevD_eq _ PeriodicComplex.BundleCycles.periodicComplexShape_true_false]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      apply Prod.ext
      · change m.1 = 0 + (c • (0 : M) + m.1) + 0
        module
      · change m.2 = 0 + (-a) • m.1 + (a • m.1 + m.2)
        module
    · rw [dNext_eq _ PeriodicComplex.BundleCycles.periodicComplexShape_true_false, prevD_eq _ PeriodicComplex.BundleCycles.periodicComplexShape_false_true]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      apply Prod.ext
      · change m.1 = 0 + ((a * b) • (0 : M) + b • (0 : M)) + m.1
        module
      · change m.2 = (c • m.1 + m.2) + (-(b * c)) • (0 : M) + (-c) • m.1
        module

def factorConeHomotopyEquiv : HomotopyEquiv (periodicFactorCone a b c h)
    (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex b (a * c) (factorCone_kill_middle a b c h)) where
  hom := factorConeProjection a b c h
  inv := factorConeSection a b c h
  homotopyHomInvId := (factorConeContraction a b c h).symm
  homotopyInvHomId := Homotopy.ofEq (factorCone_section_projection a b c h)

def factorConeHomologyIso (i : Bool) : (periodicFactorCone a b c h).homology i ≅
    (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex b (a * c) (factorCone_kill_middle a b c h)).homology i :=
  (factorConeHomotopyEquiv a b c h).toHomologyIso i

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FactorKill.BundleCycles

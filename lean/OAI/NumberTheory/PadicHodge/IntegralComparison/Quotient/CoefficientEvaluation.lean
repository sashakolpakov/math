import OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Span.Basic

/-! # Coefficient Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientEvaluation

noncomputable section

/-! Evaluation of local Ext classes on genuine quotient-module vectors.
The scalar purity isomorphism induces a canonical map to the quotient dual;
its definition uses lifts of actual coefficient maps to projective resolutions. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps

abbrev group (R : Type u) [CommRing R] (T : ModuleCat.{u} R) (n : ℕ)
    {A : ModuleCat.{u} R} (P : ProjectiveResolution A) : ModuleCat.{u} R :=
  Resolution.CohomologyMaps.cohomology (Resolution.CohomologyMaps.homFunctor R T) P n

variable (R Q : Type u) [CommRing R] [CommRing Q] [Algebra R Q]
  (hQ : Function.Surjective (algebraMap R Q))
  (T : ModuleCat.{u} R) (n : ℕ)
  (P : ProjectiveResolution (ModuleCat.of R Q))
  (e : group R T n P ≅ ModuleCat.of R Q)
  (M : Type u) [AddCommGroup M] [Module Q M] [Module R M] [IsScalarTower R Q M]
  (PM : ProjectiveResolution (ModuleCat.of R M))

def point (m : M) : ModuleCat.of R Q ⟶ ModuleCat.of R M :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton Q M m).restrictScalars R)

@[simp] theorem point_apply (m : M) (q : Q) : point R Q M m q = q • m := rfl

theorem point_add (m m' : M) : point R Q M (m + m') = point R Q M m + point R Q M m' := by
  ext q
  exact smul_add q m m'

theorem point_smul (r : R) (m : M) : point R Q M (r • m) = r • point R Q M m := by
  ext q
  exact smul_comm q r m

def evaluation (m : M) : group R T n PM ⟶ ModuleCat.of R Q :=
  Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P PM (point R Q M m) n ≫ e.hom

theorem evaluation_add (m m' : M) :
    evaluation R Q T n P e M PM (m + m') =
      evaluation R Q T n P e M PM m + evaluation R Q T n P e M PM m' := by
  simp only [evaluation, point_add, Resolution.CohomologyMaps.map_add, Preadditive.add_comp]

include hQ in
theorem evaluation_smul (q : Q) (m : M) (x : group R T n PM) :
    evaluation R Q T n P e M PM (q • m) x =
      q * evaluation R Q T n P e M PM m x := by
  obtain ⟨r, rfl⟩ := hQ q
  rw [IsScalarTower.algebraMap_smul Q r m]
  simp only [evaluation, point_smul, Resolution.CohomologyMaps.map_smul, Linear.smul_comp]
  change r • ((evaluation R Q T n P e M PM m) x) = _
  exact Algebra.smul_def r _

def dualMap : group R T n PM →ₗ[R] (M →ₗ[Q] Q) where
  toFun x :=
    { toFun := fun m => evaluation R Q T n P e M PM m x
      map_add' := fun m m' => by
        rw [evaluation_add]
        rfl
      map_smul' := fun q m => evaluation_smul R Q hQ T n P e M PM q m x }
  map_add' x y := by
    ext m
    exact (evaluation R Q T n P e M PM m).hom.map_add x y
  map_smul' r x := by
    ext m
    exact (evaluation R Q T n P e M PM m).hom.map_smul r x

@[simp] theorem dualMap_apply (x : group R T n PM) (m : M) :
    dualMap R Q hQ T n P e M PM x m = evaluation R Q T n P e M PM m x := rfl

variable (M' : Type u) [AddCommGroup M'] [Module Q M'] [Module R M'] [IsScalarTower R Q M']
  (PM' : ProjectiveResolution (ModuleCat.of R M')) (f : M →ₗ[Q] M')

theorem naturality (x : group R T n PM') (m : M) :
    dualMap R Q hQ T n P e M PM
      (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) PM PM' (ModuleCat.ofHom (f.restrictScalars R)) n x) m =
    dualMap R Q hQ T n P e M' PM' x (f m) := by
  have hf : point R Q M m ≫ ModuleCat.ofHom (f.restrictScalars R) = point R Q M' (f m) := by
    ext q
    exact f.map_smul q m
  dsimp only [dualMap_apply, evaluation]
  rw [← hf, Resolution.CohomologyMaps.map_comp]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientEvaluation

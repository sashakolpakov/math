import OAI.NumberTheory.PadicHodge.IntegralComparison.DualFrameCoefficientPurity

/-! # Coefficient Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.CoefficientPurity

noncomputable section

/-! Finite projective coefficient purity with values in the actual
scalar Ext module. No trivialization of that module is required.
The only chosen frame is a finite dual frame used to prove bijectivity. -/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientEvaluation

variable (R Q : Type u) [CommRing R] [CommRing Q] [Algebra R Q]
  (hQ : Function.Surjective (algebraMap R Q))
  (T : ModuleCat.{u} R) (n : ℕ) (P : ProjectiveResolution (ModuleCat.of R Q))
  (L : Type u) [AddCommGroup L] [Module Q L] [Module R L] [IsScalarTower R Q L]
  (eL : Quotient.CoefficientEvaluation.group R T n P ≅ ModuleCat.of R L)
  (M : Type u) [AddCommGroup M] [Module Q M] [Module R M] [IsScalarTower R Q M]
  (PM : ProjectiveResolution (ModuleCat.of R M))

def evaluation (m : M) : Quotient.CoefficientEvaluation.group R T n PM ⟶ ModuleCat.of R L :=
  Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P PM (Quotient.CoefficientEvaluation.point R Q M m) n ≫ eL.hom

omit [Module Q L] [IsScalarTower R Q L] in
theorem evaluation_add (m m' : M) :
    evaluation R Q T n P L eL M PM (m + m') =
      evaluation R Q T n P L eL M PM m + evaluation R Q T n P L eL M PM m' := by
  simp only [evaluation, Quotient.CoefficientEvaluation.point_add, Resolution.CohomologyMaps.map_add, Preadditive.add_comp]

include hQ in
theorem evaluation_smul (q : Q) (m : M) (x : Quotient.CoefficientEvaluation.group R T n PM) :
    evaluation R Q T n P L eL M PM (q • m) x =
      q • evaluation R Q T n P L eL M PM m x := by
  obtain ⟨r, rfl⟩ := hQ q
  rw [IsScalarTower.algebraMap_smul Q r m, IsScalarTower.algebraMap_smul Q]
  simp only [evaluation, Quotient.CoefficientEvaluation.point_smul, Resolution.CohomologyMaps.map_smul, Linear.smul_comp]
  rfl

def dualMap : Quotient.CoefficientEvaluation.group R T n PM →ₗ[R] (M →ₗ[Q] L) where
  toFun x :=
    { toFun := fun m => evaluation R Q T n P L eL M PM m x
      map_add' := fun m m' => by rw [evaluation_add]; rfl
      map_smul' := fun q m => evaluation_smul R Q hQ T n P L eL M PM q m x }
  map_add' x y := by ext m; exact (evaluation R Q T n P L eL M PM m).hom.map_add x y
  map_smul' r x := by ext m; exact (evaluation R Q T n P L eL M PM m).hom.map_smul r x

@[simp] theorem dualMap_apply (x : Quotient.CoefficientEvaluation.group R T n PM) (m : M) :
    dualMap R Q hQ T n P L eL M PM x m =
      eL.hom (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P PM (Quotient.CoefficientEvaluation.point R Q M m) n x) := rfl

variable (M' : Type u) [AddCommGroup M'] [Module Q M'] [Module R M'] [IsScalarTower R Q M']
  (PM' : ProjectiveResolution (ModuleCat.of R M'))

theorem naturality (f : M →ₗ[Q] M') (x : Quotient.CoefficientEvaluation.group R T n PM') (m : M) :
    dualMap R Q hQ T n P L eL M PM
        (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) PM PM' (ModuleCat.ofHom (f.restrictScalars R)) n x) m =
      dualMap R Q hQ T n P L eL M' PM' x (f m) := by
  have hf : Quotient.CoefficientEvaluation.point R Q M m ≫ ModuleCat.ofHom (f.restrictScalars R) = Quotient.CoefficientEvaluation.point R Q M' (f m) := by
    ext q
    exact f.map_smul q m
  simp only [dualMap_apply]
  rw [← hf, Resolution.CohomologyMaps.map_comp]
  rfl

theorem scalar_evaluation (x : Quotient.CoefficientEvaluation.group R T n P) (q : Q) :
    dualMap R Q hQ T n P L eL Q P x q = q • eL.hom x := by
  calc
    _ = dualMap R Q hQ T n P L eL Q P x (q • (1 : Q)) := by rw [smul_eq_mul, mul_one]
    _ = q • evaluation R Q T n P L eL Q P 1 x :=
      evaluation_smul R Q hQ T n P L eL Q P q 1 x
    _ = _ := by
      simp only [evaluation, DualFrameCoefficientPurity.point_one, Resolution.CohomologyMaps.map_id, Category.id_comp]

section Frame
variable {ι : Type u} [Fintype ι] (b : IntegralComparison.Finite.DualFrame.Frame Q M ι)
open OAI.NumberTheory.PadicHodge.IntegralComparison.DualFrameCoefficientPurity (projection sum_projection_point)

def inverse : (M →ₗ[Q] L) →ₗ[R] Quotient.CoefficientEvaluation.group R T n PM :=
  ∑ i, (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) PM P (DualFrameCoefficientPurity.projection R Q M b i) n).hom.comp
    (eL.inv.hom.comp ((LinearMap.applyₗ (R := Q) (b.vector i)).restrictScalars R))

theorem inverse_apply (f : M →ₗ[Q] L) :
    inverse R Q T n P L eL M PM b f =
      ∑ i, Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) PM P (DualFrameCoefficientPurity.projection R Q M b i) n (eL.inv (f (b.vector i))) := by
  simp only [inverse, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, LinearMap.applyₗ_apply_apply]

theorem right_inverse (f : M →ₗ[Q] L) :
    dualMap R Q hQ T n P L eL M PM (inverse R Q T n P L eL M PM b f) = f := by
  ext m
  rw [inverse_apply, _root_.map_sum]
  simp only [LinearMap.sum_apply]
  have hn (i : ι) := naturality R Q hQ T n P L eL M PM Q P
    (b.coord i) (eL.inv (f (b.vector i))) m
  calc
    _ = ∑ i, dualMap R Q hQ T n P L eL Q P (eL.inv (f (b.vector i))) (b.coord i m) :=
      Finset.sum_congr rfl (fun i _ => hn i)
    _ = ∑ i, b.coord i m • f (b.vector i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [scalar_evaluation, Iso.inv_hom_id_apply]
    _ = f m := by
      have hf := congrArg f (b.reconstruct m)
      simpa only [_root_.map_sum, LinearMap.map_smul] using hf

theorem left_inverse (x : Quotient.CoefficientEvaluation.group R T n PM) :
    inverse R Q T n P L eL M PM b (dualMap R Q hQ T n P L eL M PM x) = x := by
  rw [inverse_apply]
  have h := congrArg (fun f => Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) PM PM f n) (DualFrameCoefficientPurity.sum_projection_point R Q M b)
  rw [Resolution.CohomologyMaps.map_sum, Resolution.CohomologyMaps.map_id] at h
  simp_rw [Resolution.CohomologyMaps.map_comp _ PM P PM] at h
  have hx := ConcreteCategory.congr_hom h x
  calc
    _ = ∑ i, Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) PM P (DualFrameCoefficientPurity.projection R Q M b i) n
        (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P PM (Quotient.CoefficientEvaluation.point R Q M (b.vector i)) n x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [dualMap_apply, Iso.hom_inv_id_apply]
    _ = x := by
      simpa only [ModuleCat.comp_apply, ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.id_apply] using hx

def frameEquiv : Quotient.CoefficientEvaluation.group R T n PM ≃ₗ[R] (M →ₗ[Q] L) :=
  { dualMap R Q hQ T n P L eL M PM with
    invFun := inverse R Q T n P L eL M PM b
    left_inv := left_inverse R Q hQ T n P L eL M PM b
    right_inv := right_inverse R Q hQ T n P L eL M PM b }
end Frame

variable [Module.Finite Q M] [Module.Projective Q M]

def equiv : Quotient.CoefficientEvaluation.group R T n PM ≃ₗ[R] (M →ₗ[Q] L) :=
  LinearEquiv.ofBijective (dualMap R Q hQ T n P L eL M PM) (by
    obtain ⟨ι, hι, hb⟩ := IntegralComparison.Finite.DualFrame.exists_frame Q M
    let := hι
    exact (frameEquiv R Q hQ T n P L eL M PM hb.some).bijective)

@[simp] theorem equiv_apply (x : Quotient.CoefficientEvaluation.group R T n PM) (m : M) :
    equiv R Q hQ T n P L eL M PM x m =
      eL.hom (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P PM (Quotient.CoefficientEvaluation.point R Q M m) n x) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.CoefficientPurity

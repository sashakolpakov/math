import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupAlgebra
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorDeterminant

/-! # Graded Exterior Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GradedExteriorCup

noncomputable section

/-! Exterior cup products and their determinant action for any actual
graded cohomology family. No cosimplicial presentation is required. -/

open scoped DirectSum

section

open OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupAlgebra

universe u v

variable {R : Type u} [CommRing R] (D : GradedCupAlgebra.Data.{u,v} R)

def iterated : (n : ℕ) → (Fin n → D.H 1) → D.H n
  | 0, _ => D.one
  | n + 1, x => D.cup n 1 (iterated n (Fin.init x)) (x (Fin.last n))

theorem inclusion_iterated (n : ℕ) (x : Fin n → D.H 1) :
    GradedCupAlgebra.inclusion D n (GradedExteriorCup.iterated D n x) = (List.ofFn fun i => GradedCupAlgebra.inclusion D 1 (x i)).prod := by
  induction n with
  | zero => simp only [GradedExteriorCup.iterated, GradedCupAlgebra.inclusion_one, List.ofFn_zero, List.prod_nil]
  | succ n ih =>
      rw [GradedExteriorCup.iterated, GradedCupAlgebra.inclusion_cup, List.ofFn_succ', List.prod_concat, ih]
      rfl

def exteriorMap : ExteriorAlgebra R (D.H 1) →ₐ[R] GradedCupAlgebra.total D :=
  ExteriorAlgebra.lift R ⟨GradedCupAlgebra.inclusion D 1, GradedCupAlgebra.inclusion_square_zero D⟩

theorem exteriorMap_ι (x : D.H 1) :
    exteriorMap D (ExteriorAlgebra.ι R x) = GradedCupAlgebra.inclusion D 1 x :=
  ExteriorAlgebra.lift_ι_apply R _ _ x

theorem exteriorMap_multi (n : ℕ) (x : Fin n → D.H 1) :
    exteriorMap D (ExteriorAlgebra.ιMulti R n x) = GradedCupAlgebra.inclusion D n (GradedExteriorCup.iterated D n x) := by
  rw [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn, inclusion_iterated]
  congr 2
  funext i
  exact exteriorMap_ι D (x i)

def exteriorPowerCup (n : ℕ) : (⋀[R]^n (D.H 1)) →ₗ[R] D.H n :=
  (GradedCupAlgebra.component D n).comp ((exteriorMap D).toLinearMap.comp
    (Submodule.subtype (⋀[R]^n (D.H 1))))

theorem exteriorPowerCup_multi (n : ℕ) (x : Fin n → D.H 1) :
    exteriorPowerCup D n (exteriorPower.ιMulti R n x) = GradedExteriorCup.iterated D n x := by
  change GradedCupAlgebra.component D n (exteriorMap D (ExteriorAlgebra.ιMulti R n x)) = _
  rw [exteriorMap_multi]
  exact DirectSum.component.lof_self R n _

theorem exteriorPowerCup_ne_zero (n : ℕ) (x : Fin n → D.H 1) (hx : GradedExteriorCup.iterated D n x ≠ 0) :
    exteriorPowerCup D n ≠ 0 := by
  intro h
  apply hx
  rw [← exteriorPowerCup_multi, h]
  rfl

variable (f : ∀ n, Module.End R (D.H n))
  (hunit : f 0 D.one = D.one)
  (hcup : ∀ i j (x : D.H i) (y : D.H j),
    f (i + j) (D.cup i j x y) = D.cup i j (f i x) (f j y))

include hunit hcup in
theorem iterated_natural (n : ℕ) (x : Fin n → D.H 1) :
    f n (GradedExteriorCup.iterated D n x) = GradedExteriorCup.iterated D n (fun i => f 1 (x i)) := by
  induction n with
  | zero => exact hunit
  | succ n ih => simp only [GradedExteriorCup.iterated, hcup, ih]; rfl

include hunit hcup in
theorem exteriorPowerCup_natural (n : ℕ) :
    (f n).comp (exteriorPowerCup D n) =
      (exteriorPowerCup D n).comp (exteriorPower.map n (f 1)) := by
  apply LinearMap.ext_on (exteriorPower.ιMulti_span R n (D.H 1))
  rintro w ⟨x, rfl⟩
  simp only [LinearMap.comp_apply, exteriorPower.map_apply_ιMulti, exteriorPowerCup_multi]
  exact iterated_natural D f hunit hcup n x

end

open OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupAlgebra

universe u v

variable {K : Type u} [Field K] (D : GradedCupAlgebra.Data.{u,v} K)
  [FiniteDimensional K (D.H 1)]
  (f : ∀ n, Module.End K (D.H n))
  (hunit : f 0 D.one = D.one)
  (hcup : ∀ i j (x : D.H i) (y : D.H j),
    f (i + j) (D.cup i j x y) = D.cup i j (f i x) (f j y))

local notation "n" => Module.finrank K (D.H 1)

include hunit hcup in
theorem top_cup_action (z : ⋀[K]^n (D.H 1)) :
    f n (exteriorPowerCup D n z) = (f 1).det • exteriorPowerCup D n z := by
  have h := LinearMap.congr_fun (exteriorPowerCup_natural D f hunit hcup n) z
  change f n (exteriorPowerCup D n z) = exteriorPowerCup D n (exteriorPower.map n (f 1) z) at h
  rw [TopExteriorDeterminant.map_top_eq_det_smul,
    LinearMap.smul_apply, LinearMap.id_apply, map_smul] at h
  exact h

include hunit hcup in
theorem det_eq_of_top_scalar (c : K) (hprod : exteriorPowerCup D n ≠ 0)
    (htop : ∀ x : D.H n, f n x = c • x) : (f 1).det = c := by
  classical
  have hz : ∃ z, exteriorPowerCup D n z ≠ 0 := by
    by_contra! hz
    exact hprod (LinearMap.ext hz)
  obtain ⟨z, hz⟩ := hz
  apply smul_left_injective K hz
  exact (top_cup_action D f hunit hcup z).symm.trans (htop (exteriorPowerCup D n z))

include hunit hcup in
theorem det_eq_of_nonzero_iterated (c : K) (v : Fin n → D.H 1)
    (hv : GradedExteriorCup.iterated D n v ≠ 0) (htop : ∀ x : D.H n, f n x = c • x) : (f 1).det = c :=
  det_eq_of_top_scalar D f hunit hcup c (exteriorPowerCup_ne_zero D n v hv) htop

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GradedExteriorCup

import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorCoordinates
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Koszul Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulComplex

noncomputable section

/-! The actual exterior Koszul chain complex and its functoriality in the
module of generators. Its differential is contraction by the equation map. -/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction

universe u
variable (R : Type u) [CommRing R]
  (V W : Type u) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem contraction_square (s : Module.Dual R V) (n : ℕ) :
    (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V s n).comp (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V s (n + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact CliffordAlgebra.contractLeft_contractLeft s x.val

def complex (s : Module.Dual R V) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (⋀[R]^n V))
    (fun n => ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V s n))
    (fun n => ModuleCat.hom_ext (contraction_square R V s n))

variable (s : Module.Dual R V) (t : Module.Dual R W) (f : V →ₗ[R] W)
  (h : t.comp f = s)

theorem map_coe (n : ℕ) (x : ⋀[R]^n V) :
    (exteriorPower.map n f x : ExteriorAlgebra R W) = ExteriorAlgebra.map f x.val := by
  have he : (⋀[R]^n W).subtype.comp (exteriorPower.map n f) =
      (ExteriorAlgebra.map f).toLinearMap.comp (⋀[R]^n V).subtype := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span R n V)
    rintro x ⟨v, rfl⟩
    simp only [LinearMap.comp_apply, exteriorPower.map_apply_ιMulti]
    exact (ExteriorAlgebra.map_apply_ιMulti f v).symm
  exact LinearMap.congr_fun he x

include h in
theorem ambient_naturality (x : ExteriorAlgebra R V) :
    AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R W t (ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map f (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R V s x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap a => simp [AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction, CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction_ι_mul,
      map_sub, map_smul, hx]
    rw [show t (f v) = s v from LinearMap.congr_fun h v]

include h in
theorem contraction_naturality (n : ℕ) :
    (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R W t n).comp (exteriorPower.map (n + 1) f) =
      (exteriorPower.map n f).comp (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V s n) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.ambientContraction R W t (exteriorPower.map (n + 1) f x).val =
    (exteriorPower.map n f (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.contraction R V s n x)).val
  rw [map_coe, map_coe]
  exact ambient_naturality R V W s t f h x.val

def map (h : t.comp f = s) : complex R V s ⟶ complex R W t where
  f n := ModuleCat.ofHom (exteriorPower.map n f)
  comm' i j hij := by
    have hi : j + 1 = i := hij
    subst i
    dsimp only [complex]
    rw [ChainComplex.of_d, ChainComplex.of_d]
    exact ModuleCat.hom_ext (contraction_naturality R V W s t f h j)

theorem map_top {n : ℕ} (b : Module.Basis (Fin n) R V)
    (s t : Module.Dual R V) (f : Module.End R V) (h : t.comp f = s) :
    (KoszulComplex.map R V V s t f h).f n =
      ModuleCat.ofHom (f.det • (LinearMap.id : (⋀[R]^n V) →ₗ[R] (⋀[R]^n V))) := by
  exact congrArg ModuleCat.ofHom (TopExteriorDeterminant.map_eq_det_smul_of_basis b f)

theorem dual_top {n : ℕ} (b : Module.Basis (Fin n) R V)
    (s t : Module.Dual R V) (f : Module.End R V) (h : t.comp f = s)
    (a : Module.Dual R (⋀[R]^n V)) :
    a.comp ((KoszulComplex.map R V V s t f h).f n).hom = f.det • a := by
  rw [map_top R V b]
  apply LinearMap.ext
  intro x
  exact a.map_smul f.det x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulComplex

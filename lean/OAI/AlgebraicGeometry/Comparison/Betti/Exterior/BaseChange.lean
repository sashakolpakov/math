import OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Exterior.BaseChange

noncomputable section

/-! Exterior powers preserve scalar extension for free modules, with the actual induced map. -/

open scoped TensorProduct

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

theorem isBaseChange_of_basis_map {ι : Type*} (f : M →ₗ[R] N)
    (b : Module.Basis ι R M) (c : Module.Basis ι S N)
    (h : ∀ i, f (b i) = c i) : IsBaseChange S f := by
  let t : M →ₗ[R] S ⊗[R] M := TensorProduct.mk R S M 1
  let hb : IsBaseChange S t := TensorProduct.isBaseChange R M S
  let b' := hb.basis b
  let e : S ⊗[R] M ≃ₗ[S] N := b'.equiv c (Equiv.refl ι)
  apply IsBaseChange.of_equiv e
  have he : (e.toLinearMap.restrictScalars R).comp t = f := by
    apply b.ext
    intro i
    change e (t (b i)) = f (b i)
    rw [← hb.basis_apply b i]
    change (b'.equiv c (Equiv.refl ι)) (b' i) = _
    rw [Module.Basis.equiv_apply]
    exact (h i).symm
  exact fun x => LinearMap.congr_fun he x

def map (f : M →ₗ[R] N) (n : ℕ) : ⋀[R]^n M →ₗ[R] ⋀[S]^n N :=
  exteriorPower.alternatingMapLinearEquiv
    ((Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.restrictAlternating (R := R)
      (exteriorPower.ιMulti S n)).compLinearMap f)

theorem map_mk (f : M →ₗ[R] N) (n : ℕ) (v : Fin n → M) :
    map f n (exteriorPower.ιMulti R n v) = exteriorPower.ιMulti S n (fun i => f (v i)) := by
  simp [map, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem map_basis {ι : Type*} [LinearOrder ι] (f : M →ₗ[R] N)
    (h : IsBaseChange S f) (b : Module.Basis ι R M) (n : ℕ)
    (s : Set.powersetCard ι n) :
    map f n (b.exteriorPower n s) = (h.basis b).exteriorPower n s := by
  rw [exteriorPower.basis_apply, exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  rw [map_mk]
  congr 1
  funext i
  exact (h.basis_apply b _).symm

theorem isBaseChange {ι : Type*} [LinearOrder ι] (f : M →ₗ[R] N)
    (h : IsBaseChange S f) (b : Module.Basis ι R M) (n : ℕ) :
    IsBaseChange S (map (S := S) f n) :=
  isBaseChange_of_basis_map (map (S := S) f n) (b.exteriorPower n) ((h.basis b).exteriorPower n)
    (map_basis f h b n)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Exterior.BaseChange

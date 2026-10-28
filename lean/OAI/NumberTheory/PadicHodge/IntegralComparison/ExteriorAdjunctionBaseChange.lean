import OAI.NumberTheory.PadicHodge.IntegralComparison.SplitExteriorAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # Exterior Adjunction Base Change -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.ExteriorAdjunctionBaseChange.Split

/-! The splitting-independent top-form residue commutes with arbitrary
scalar extension of a split sequence of finite free modules. -/

open _root_.Module
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.SplitExteriorAdjunction OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorCoordinates

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {U : Type*} [AddCommGroup U] [Module R U]
  {W : Type*} [AddCommGroup W] [Module R W]
  {V : Type*} [AddCommGroup V] [Module R V]
  {c g : ℕ} (bU : Basis (Fin c) R U) (bW : Basis (Fin g) R W)
  (e : (U × W) ≃ₗ[R] V)

def splitting : ((S ⊗[R] U) × (S ⊗[R] W)) ≃ₗ[S] S ⊗[R] V :=
  (TensorProduct.prodRight R S S U W).symm.trans (e.baseChange R S (U × W) V)

theorem splitting_tmul (a : S) (u : U) (w : W) :
    splitting S e (a ⊗ₜ[R] u, a ⊗ₜ[R] w) = a ⊗ₜ[R] e (u, w) := by
  simp only [splitting, LinearEquiv.trans_apply, TensorProduct.prodRight_symm_tmul,
    LinearEquiv.baseChange_tmul]

theorem splitting_left_tmul (a : S) (u : U) :
    splitting S e (a ⊗ₜ[R] u, 0) = a ⊗ₜ[R] e (u, 0) := by
  simpa only [TensorProduct.tmul_zero] using splitting_tmul S e a u 0

theorem splitting_right_tmul (a : S) (w : W) :
    splitting S e (0, a ⊗ₜ[R] w) = a ⊗ₜ[R] e (0, w) := by
  simpa only [TensorProduct.tmul_zero] using splitting_tmul S e a 0 w

theorem splitting_symm_tmul (a : S) (v : V) :
    (splitting S e).symm (a ⊗ₜ[R] v) =
      (a ⊗ₜ[R] (e.symm v).1, a ⊗ₜ[R] (e.symm v).2) := by
  simp only [splitting, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_symm_tmul, LinearEquiv.symm_symm, TensorProduct.prodRight_tmul]

theorem productBasis_baseChange :
    SplitExteriorAdjunction.productBasis (bU.baseChange S) (bW.baseChange S) (splitting S e) =
      (SplitExteriorAdjunction.productBasis bU bW e).baseChange S := by
  apply DFunLike.ext
  intro j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases j with
  | inl j =>
    simp only [SplitExteriorAdjunction.productBasis, Basis.reindex_apply, Basis.map_apply,
      Equiv.symm_apply_apply, Basis.prod_apply, Sum.elim_inl, Function.comp_apply,
      LinearMap.inl_apply, Basis.baseChange_apply]
    exact splitting_left_tmul S e 1 (bU j)
  | inr j =>
    simp only [SplitExteriorAdjunction.productBasis, Basis.reindex_apply, Basis.map_apply,
      Equiv.symm_apply_apply, Basis.prod_apply, Sum.elim_inr, Function.comp_apply,
      LinearMap.inr_apply, Basis.baseChange_apply]
    exact splitting_right_tmul S e 1 (bW j)

theorem powerScalarMap_generator {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ} (b : Basis (Fin n) R M) :
    GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap R S M n (1 ⊗ₜ[R] TopExteriorCoordinates.generator b) = TopExteriorCoordinates.generator (b.baseChange S) := by
  rw [TopExteriorCoordinates.generator, GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap_tmul_ιMulti, one_smul]
  congr 1
  funext i
  exact (Basis.baseChange_apply S b i).symm

theorem residue_baseChange :
    (SplitExteriorAdjunction.residue (bU.baseChange S) (bW.baseChange S) (splitting S e)).toLinearMap.comp
      (GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap R S V (c + g)) =
      (GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap R S W g).comp ((SplitExteriorAdjunction.residue bU bW e).toLinearMap.baseChange S) := by
  apply ((TopExteriorBaseChange.topBasis (SplitExteriorAdjunction.productBasis bU bW e)).baseChange S).ext
  intro j
  simp only [Basis.baseChange_apply, TopExteriorBaseChange.topBasis_apply,
    LinearMap.comp_apply, LinearMap.baseChange_tmul]
  change SplitExteriorAdjunction.residue (bU.baseChange S) (bW.baseChange S) (splitting S e)
    (GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap R S V (c + g) (1 ⊗ₜ[R] TopExteriorCoordinates.generator (SplitExteriorAdjunction.productBasis bU bW e))) =
      GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap R S W g (1 ⊗ₜ[R] SplitExteriorAdjunction.residue bU bW e (TopExteriorCoordinates.generator (SplitExteriorAdjunction.productBasis bU bW e)))
  rw [powerScalarMap_generator, ← productBasis_baseChange, SplitExteriorAdjunction.residue_generator,
    SplitExteriorAdjunction.residue_generator, powerScalarMap_generator]

end NumberTheory.PadicHodge.IntegralComparison.ExteriorAdjunctionBaseChange.Split

namespace NumberTheory.PadicHodge.IntegralComparison.ExteriorAdjunctionBaseChange.SplitNaturality

/-! Naturality of the canonical top-form residue for isomorphisms of
split short exact sequences. No equality of the chosen splittings is required. -/

open _root_.Module

open OAI.NumberTheory.PadicHodge.IntegralComparison.SplitExteriorAdjunction OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorCoordinates

variable {R : Type*} [CommRing R]
  {U : Type*} [AddCommGroup U] [Module R U]
  {W : Type*} [AddCommGroup W] [Module R W]
  {V : Type*} [AddCommGroup V] [Module R V]
  {U' : Type*} [AddCommGroup U'] [Module R U']
  {W' : Type*} [AddCommGroup W'] [Module R W']
  {V' : Type*} [AddCommGroup V'] [Module R V']
  {c g : ℕ} (bU : Basis (Fin c) R U) (bW : Basis (Fin g) R W)
  (e : (U × W) ≃ₗ[R] V)
  (fU : U ≃ₗ[R] U') (fW : W ≃ₗ[R] W') (fV : V ≃ₗ[R] V')

def splitting : (U' × W') ≃ₗ[R] V' :=
  (fU.symm.prodCongr fW.symm).trans (e.trans fV)

theorem productBasis_map :
    SplitExteriorAdjunction.productBasis (bU.map fU) (bW.map fW) (splitting e fU fW fV) =
      (SplitExteriorAdjunction.productBasis bU bW e).map fV := by
  apply DFunLike.ext
  intro j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases j <;>
    simp [SplitExteriorAdjunction.productBasis, Basis.prod_apply, splitting]

theorem map_generator {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {n : ℕ} (b : Basis (Fin n) R M) (f : M ≃ₗ[R] N) :
    exteriorPower.map n f.toLinearMap (TopExteriorCoordinates.generator b) = TopExteriorCoordinates.generator (b.map f) := by
  rw [TopExteriorCoordinates.generator, exteriorPower.map_apply_ιMulti]
  rfl

theorem residue_transport :
    (SplitExteriorAdjunction.residue (bU.map fU) (bW.map fW) (splitting e fU fW fV)).toLinearMap.comp
      (exteriorPower.map (c + g) fV.toLinearMap) =
      (exteriorPower.map g fW.toLinearMap).comp (SplitExteriorAdjunction.residue bU bW e).toLinearMap := by
  apply (TopExteriorBaseChange.topBasis (SplitExteriorAdjunction.productBasis bU bW e)).ext
  intro j
  simp only [TopExteriorBaseChange.topBasis_apply, LinearMap.comp_apply]
  change SplitExteriorAdjunction.residue (bU.map fU) (bW.map fW) (splitting e fU fW fV)
      (exteriorPower.map (c + g) fV.toLinearMap (TopExteriorCoordinates.generator (SplitExteriorAdjunction.productBasis bU bW e))) =
    exteriorPower.map g fW.toLinearMap (SplitExteriorAdjunction.residue bU bW e (TopExteriorCoordinates.generator (SplitExteriorAdjunction.productBasis bU bW e)))
  rw [map_generator, ← productBasis_map bU bW e fU fW fV,
    SplitExteriorAdjunction.residue_generator, SplitExteriorAdjunction.residue_generator, map_generator]

variable (e' : (U' × W') ≃ₗ[R] V')
  (hU : ∀ u, fV (e (u, 0)) = e' (fU u, 0))
  (hW : ∀ v, fW (e.symm v).2 = (e'.symm (fV v)).2)

include hU hW in
theorem residue_splitting :
    SplitExteriorAdjunction.residue (bU.map fU) (bW.map fW) (splitting e fU fW fV) =
      SplitExteriorAdjunction.residue (bU.map fU) (bW.map fW) e' := by
  apply SplitExteriorAdjunction.residue_independent_splitting
  · intro u
    simpa only [splitting, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      map_zero, LinearEquiv.apply_symm_apply] using hU (fU.symm u)
  · intro v
    simpa only [splitting, LinearEquiv.trans_symm, LinearEquiv.prodCongr_symm,
      LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.symm_symm,
      LinearEquiv.apply_symm_apply]
      using hW (fV.symm v)

include hU hW in
theorem residue_naturality :
    (SplitExteriorAdjunction.residue (bU.map fU) (bW.map fW) e').toLinearMap.comp
      (exteriorPower.map (c + g) fV.toLinearMap) =
      (exteriorPower.map g fW.toLinearMap).comp (SplitExteriorAdjunction.residue bU bW e).toLinearMap := by
  rw [← residue_splitting bU bW e fU fW fV e' hU hW]
  exact residue_transport bU bW e fU fW fV

end NumberTheory.PadicHodge.IntegralComparison.ExteriorAdjunctionBaseChange.SplitNaturality

end

end OAI

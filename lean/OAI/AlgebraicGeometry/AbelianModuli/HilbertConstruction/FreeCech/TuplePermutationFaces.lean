/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleAlternation

/-! # Tuple Permutation Faces -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TuplePermutationFaces

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

theorem cechTupleAlternatingProjection_boundary_single_of_strictMono
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 2) → ι) (hi : StrictMono i) :
    TupleChains.cechTupleBoundary n
        (TupleAlternation.cechTupleAlternatingProjection (n + 1) (Finsupp.single i 1)) =
      TupleAlternation.cechTupleAlternatingProjection n
        (TupleChains.cechTupleBoundary n (Finsupp.single i 1)) := by
  rw [TupleAlternation.cechTupleAlternatingProjection_single,
    TupleAlternation.cechTupleAlternatingProjectionBasis_of_strictMono i hi, one_smul]
  simp only [TupleChains.cechTupleBoundary_single, one_smul]
  unfold TupleChains.cechTupleBoundaryBasis
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [TupleAlternation.cechTupleAlternatingProjection_single,
    TupleAlternation.cechTupleAlternatingProjectionBasis_of_strictMono]
  · simp
  · exact hi.comp (Fin.strictMono_succAbove k)

theorem cechTupleDelete_comp_cechPermDelete
    {ι : Type u} {n : ℕ} (i : Fin (n + 2) → ι)
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    TupleChains.cechTupleDelete i (σ r) ∘
        Cech.PermutedTupleSigns.cechPermDelete σ r =
      TupleChains.cechTupleDelete (i ∘ σ) r := by
  funext x
  exact congrArg i
    (Cech.PermutedTupleSigns.succAbove_cechPermDelete σ r x)

theorem cechTupleAlternatingProjectionBasis_delete_perm
    {ι : Type u} [LinearOrder ι] {n : ℕ}
    (i : Fin (n + 2) → ι) (σ : Equiv.Perm (Fin (n + 2)))
    (hiσ : StrictMono (i ∘ σ)) (r : Fin (n + 2)) :
    TupleAlternation.cechTupleAlternatingProjectionBasis n (TupleChains.cechTupleDelete i (σ r)) =
      (Equiv.Perm.sign
          (Cech.PermutedTupleSigns.cechPermDelete σ r) : ℤ) •
        Finsupp.single (TupleChains.cechTupleDelete (i ∘ σ) r) 1 := by
  let ρ := Cech.PermutedTupleSigns.cechPermDelete σ r
  have htuple :
      TupleChains.cechTupleDelete i (σ r) ∘ ρ =
        TupleChains.cechTupleDelete (i ∘ σ) r :=
    cechTupleDelete_comp_cechPermDelete i σ r
  have hperm :=
    TupleAlternation.cechTupleAlternatingProjectionBasis_comp_perm
      (TupleChains.cechTupleDelete i (σ r)) ρ
  rw [htuple, TupleAlternation.cechTupleAlternatingProjectionBasis_of_strictMono
    (TupleChains.cechTupleDelete (i ∘ σ) r)
    (hiσ.comp (Fin.strictMono_succAbove r))] at hperm
  have hs :
      (Equiv.Perm.sign ρ : ℤ) * (Equiv.Perm.sign ρ : ℤ) = 1 :=
    Int.units_coe_mul_self (Equiv.Perm.sign ρ)
  calc
    TupleAlternation.cechTupleAlternatingProjectionBasis n (TupleChains.cechTupleDelete i (σ r)) =
        1 • TupleAlternation.cechTupleAlternatingProjectionBasis n
          (TupleChains.cechTupleDelete i (σ r)) := by rw [one_smul]
    _ = ((Equiv.Perm.sign ρ : ℤ) * (Equiv.Perm.sign ρ : ℤ)) •
        TupleAlternation.cechTupleAlternatingProjectionBasis n
          (TupleChains.cechTupleDelete i (σ r)) :=
      congrArg (fun a : ℤ => a •
        TupleAlternation.cechTupleAlternatingProjectionBasis n
          (TupleChains.cechTupleDelete i (σ r))) hs.symm
    _ = (Equiv.Perm.sign ρ : ℤ) •
        ((Equiv.Perm.sign ρ : ℤ) •
          TupleAlternation.cechTupleAlternatingProjectionBasis n
            (TupleChains.cechTupleDelete i (σ r))) := by rw [smul_smul]
    _ = (Equiv.Perm.sign ρ : ℤ) •
        Finsupp.single (TupleChains.cechTupleDelete (i ∘ σ) r) 1 :=
      congrArg ((Equiv.Perm.sign ρ : ℤ) • ·) hperm.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TuplePermutationFaces

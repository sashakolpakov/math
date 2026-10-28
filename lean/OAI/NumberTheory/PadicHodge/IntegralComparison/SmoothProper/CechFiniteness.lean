import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechScalarSystem
import OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarInverseResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdicFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Coefficient

/-! # Cech Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechFiniteness

noncomputable section

/-! The compatible inverse limit of native Witt Čech cohomology is finitely generated over its original coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionData

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (i : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "A" => (fun n : ℕ => ModuleCat.carrier (HomologicalComplex.homology (OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTransitionData.complex p k X n) i))
local notation "t" => (fun n : ℕ => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechScalarSystem.map p k X n (n + 1) (Nat.le_succ n) i)
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarInverseResidue.compatible R A t

include hprojective in
theorem residue_finite : Finite (L ⧸ ((Ideal.span {(p : R)}) • (⊤ : Submodule R L))) := by
  let (n : ℕ) : Finite (A n) := CechScalarSystem.finite p k X hprojective n i
  exact ScalarInverseResidue.finite_residue R (p : R) A t
    (fun n => CechScalarSystem.inclusion p k X n i)
    (fun n => CechScalarSystem.map p k X 0 n (Nat.zero_le n) i)
    (fun n x => CechScalarSystem.inclusion_map p k X n i x)
    (fun n x => CechScalarSystem.map_inclusion p k X n i x)
    (CechScalarSystem.identity p k X 0 i)
    (fun n x => CechScalarSystem.composition p k X 0 n (n + 1)
      (Nat.zero_le n) (Nat.le_succ n) i x)
    (fun n x => CechScalarSystem.exact p k X n i x)
    (fun x => by simpa only [zero_add, pow_one] using CechScalarSystem.power_zero p k X 0 i x)

theorem separated : IsHausdorff (Ideal.span {(p : R)}) L :=
  Principal.AdicModules.hausdorff R (p : R) A L
    (fun n x => CechScalarSystem.power_zero p k X n i x)

include hprojective in
theorem cech_finite : Module.Finite R L := by
  let : IsAdicComplete (Ideal.span {(p : R)}) R := Witt.Coefficient.coefficient p k
  let : IsHausdorff (Ideal.span {(p : R)}) L := separated p k X i
  let : Finite (L ⧸ ((Ideal.span {(p : R)}) • (⊤ : Submodule R L))) := residue_finite p k X hprojective i
  exact Principal.AdicFiniteness.finite R (p : R) L

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechFiniteness

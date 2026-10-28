import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.LinearCombination

/-! # Lattice Semicharacter -/

namespace OAI.RepresentationTheory.Theta.Geometric.LatticeSemicharacter

noncomputable section

/-! An integral basis constructs a semicharacter for every integral
alternating form; the original polarization need not be doubled. -/

variable {L I : Type} [AddCommGroup L] [Module ℤ L] [LinearOrder I]
  (b : Module.Basis I ℤ L) (B : LinearMap.BilinForm ℤ L)

def upperLatticeForm : LinearMap.BilinForm ℤ L :=
  b.constr ℤ (fun i => b.constr ℤ (fun j => if i < j then B (b i) (b j) else 0))

@[simp] theorem upperLatticeForm_basis (i j : I) :
    upperLatticeForm b B (b i) (b j) = if i < j then B (b i) (b j) else 0 := by
  simp only [upperLatticeForm, Module.Basis.constr_basis]

theorem upperLatticeForm_sub_flip (hB : B.IsAlt) :
    upperLatticeForm b B - (upperLatticeForm b B).flip = B := by
  apply b.ext
  intro i
  apply b.ext
  intro j
  simp only [LinearMap.sub_apply, LinearMap.BilinForm.flip_apply, upperLatticeForm_basis]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp only [hij, not_lt.mpr hij.le, ite_true, ite_false, sub_zero]
  · simp only [lt_irrefl, ite_false, sub_self, hB (b i)]
  · simp only [hji, not_lt.mpr hji.le, ite_true, ite_false, zero_sub]
    exact LinearMap.BilinForm.IsAlt.neg_eq hB (b j) (b i)

def latticeQuadraticRefinement (v : L) : ℤ := upperLatticeForm b B v v

theorem latticeQuadraticRefinement_add (hB : B.IsAlt) (v w : L) :
    latticeQuadraticRefinement b B (v + w) =
      latticeQuadraticRefinement b B v + latticeQuadraticRefinement b B w + B v w +
        2 * upperLatticeForm b B w v := by
  have h := LinearMap.congr_fun (LinearMap.congr_fun (upperLatticeForm_sub_flip b B hB) v) w
  change upperLatticeForm b B v w - upperLatticeForm b B w v = B v w at h
  simp only [latticeQuadraticRefinement, map_add, LinearMap.add_apply]
  omega

def latticeSemicharacter (v : L) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * (latticeQuadraticRefinement b B v : ℂ))

theorem latticeSemicharacter_ne_zero (v : L) : latticeSemicharacter b B v ≠ 0 :=
  Complex.exp_ne_zero _

@[simp] theorem latticeSemicharacter_zero : latticeSemicharacter b B 0 = 1 := by
  simp [latticeSemicharacter, latticeQuadraticRefinement]

theorem latticeSemicharacter_add (hB : B.IsAlt) (v w : L) :
    latticeSemicharacter b B (v + w) = latticeSemicharacter b B v * latticeSemicharacter b B w *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (B v w : ℂ)) := by
  have h := latticeQuadraticRefinement_add b B hB v w
  unfold latticeSemicharacter
  rw [← Complex.exp_add, ← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨upperLatticeForm b B w v, ?_⟩
  have hc := congrArg (fun n : ℤ => (n : ℂ)) h
  push_cast at hc
  linear_combination (Real.pi : ℂ) * Complex.I * hc

end

end OAI.RepresentationTheory.Theta.Geometric.LatticeSemicharacter

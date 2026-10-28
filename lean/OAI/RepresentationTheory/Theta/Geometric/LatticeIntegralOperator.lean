import OAI.RepresentationTheory.Theta.Geometric.PolynomialIntertwining
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Lattice Integral Operator -/

namespace OAI.RepresentationTheory.Theta.Geometric.LatticeIntegralOperator

noncomputable section

/-! Preserving an actual full integral lattice makes a rational or
number-field-linear operator integral over the integers. The annihilating
polynomial is the characteristic polynomial of its lattice restriction. -/

open _root_.Polynomial

theorem lattice_operator_isIntegral {E V I : Type*} [Field E] [Algebra ℚ E]
    [AddCommGroup V] [Module ℚ V] [Module E V] [IsScalarTower ℚ E V] [Fintype I]
    (L : Submodule ℤ V) (b : Module.Basis I ℤ L)
    (hspan : Submodule.span ℚ (L : Set V) = ⊤) (f : Module.End E V)
    (hf : ∀ x ∈ L, f x ∈ L) : IsIntegral ℤ f := by
  let : Module.Finite ℤ L := Module.Finite.of_basis b
  let : Module.Free ℤ L := Module.Free.of_basis b
  let g : Module.End ℤ L := (f.restrictScalars ℤ).restrict hf
  have hz (x : L) : aeval f g.charpoly x.val = 0 := by
    have h := PolynomialIntertwining.polynomial_intertwining_apply g f L.subtype (fun _ => rfl) g.charpoly x
    rw [g.aeval_self_charpoly, LinearMap.zero_apply, map_zero] at h
    exact h
  have he : (aeval f g.charpoly).restrictScalars ℚ = 0 := by
    apply LinearMap.ext_on hspan
    intro x hx
    exact hz ⟨x, hx⟩
  refine ⟨g.charpoly, g.charpoly_monic, ?_⟩
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun he x

end

end OAI.RepresentationTheory.Theta.Geometric.LatticeIntegralOperator

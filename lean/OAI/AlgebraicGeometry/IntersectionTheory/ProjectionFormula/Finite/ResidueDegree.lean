import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ResidueDegree
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Residue Degree -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ResidueDegree

noncomputable section

/-! Every point of a finite scheme morphism has positive native
residue degree, by comparison with the finite algebra on an affine chart. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem positive {X Y : Scheme} (f : X ⟶ Y) [IsFinite f] (x : X) : 0 < f.residueDegree x := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top (f x))
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let φ : R →+* S := (f.app U).hom
  let : Algebra R S := φ.toAlgebra
  let : Module.Finite R S := f.finite_app U hU
  let q : PrimeSpectrum S := hV.primeIdealOf ⟨x, hxU⟩
  have hq : hV.fromSpec q = x := hV.fromSpec_primeIdealOf _
  have hfac : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ hU.fromSpec = hV.fromSpec ≫ f := by
    change Spec.map (f.app U) ≫ hU.fromSpec = hV.fromSpec ≫ f
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl
  rw [← hq, ← Support.Map.residueDegree_pre_immersion hV.fromSpec f q, ← hfac,
    Support.Map.residueDegree_post_immersion, Affine.ResidueDegree.residueDegree_eq_inertiaDeg]
  exact q.asIdeal.inertiaDeg_pos R

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ResidueDegree

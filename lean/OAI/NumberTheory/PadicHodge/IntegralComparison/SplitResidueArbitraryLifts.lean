import OAI.NumberTheory.PadicHodge.IntegralComparison.SplitExteriorAdjunction

/-! # Split Residue Arbitrary Lifts -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SplitResidueArbitraryLifts

noncomputable section

/-! Conormal residue of the normal wedge followed by arbitrary lifts
of a quotient basis is exactly its quotient wedge. No chosen lift is
required to agree with the auxiliary splitting. -/
open _root_.Module
universe u v w t
variable {R : Type u} [CommRing R]
  {U : Type v} [AddCommGroup U] [Module R U]
  {W : Type w} [AddCommGroup W] [Module R W]
  {V : Type t} [AddCommGroup V] [Module R V]

def shear (a : W →ₗ[R] U) : (U × W) ≃ₗ[R] (U × W) where
  toFun z := (z.1 + a z.2, z.2)
  invFun z := (z.1 - a z.2, z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' z z' := by ext <;> simp [add_assoc, add_comm, add_left_comm]
  map_smul' r z := by ext <;> simp [smul_add]

variable {c g : ℕ} (bU : Basis (Fin c) R U) (bW : Basis (Fin g) R W)
  (e : (U × W) ≃ₗ[R] V) (v : Fin g → V)
  (hv : ∀ i, (e.symm (v i)).2 = bW i)

def adapted : (U × W) ≃ₗ[R] V :=
  (shear (bW.constr R (fun i => (e.symm (v i)).1))).trans e

theorem adapted_normal (u : U) : adapted bW e v (u, 0) = e (u, 0) := by
  simp [adapted, shear]

theorem adapted_quotient (x : V) : ((adapted bW e v).symm x).2 = (e.symm x).2 := rfl

include hv in
theorem adapted_basis (i : Fin g) : adapted bW e v (0, bW i) = v i := by
  change e (0 + (bW.constr R (fun j => (e.symm (v j)).1)) (bW i), bW i) = v i
  rw [Basis.constr_basis, zero_add, ← hv i]
  exact e.apply_symm_apply (v i)

include hv in
theorem productBasis_append :
    (SplitExteriorAdjunction.productBasis bU bW (adapted bW e v) : Fin (c + g) → V) =
      Fin.append (fun i => e (bU i, 0)) v := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa [SplitExteriorAdjunction.productBasis, Basis.reindex_apply,
      Basis.map_apply, Basis.prod_apply]
      using adapted_normal bW e v (bU j)
  · simpa [SplitExteriorAdjunction.productBasis, Basis.reindex_apply,
      Basis.map_apply, Basis.prod_apply]
      using adapted_basis bW e v hv j

include hv in
theorem residue_wedge : SplitExteriorAdjunction.residue bU bW e
    (exteriorPower.ιMulti R (c + g) (Fin.append (fun i => e (bU i, 0)) v)) =
      exteriorPower.ιMulti R g bW := by
  rw [← productBasis_append bU bW e v hv]
  have he := SplitExteriorAdjunction.residue_independent_splitting bU bW e
    (adapted bW e v) (fun u => (adapted_normal bW e v u).symm)
      (fun x => (adapted_quotient bW e v x).symm)
  rw [he]
  exact SplitExteriorAdjunction.residue_generator bU bW (adapted bW e v)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SplitResidueArbitraryLifts

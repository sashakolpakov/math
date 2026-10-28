import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ConormalDerivations
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Conormal Eigenquotient -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConormalEigenquotient

noncomputable section

section

/-! A finite family of conormal equations has one actual quotient.
Its coefficient-fiber dimension is the dimension of the dual eigenfunctionals. -/

open scoped TensorProduct

variable {R V ι : Type} [CommRing R] [AddCommGroup V] [Module R V]
  (d : ι → Module.End R V) (t : ι → R)

def conormalEigenRelations : Submodule R V := ⨆ i, (d i - t i • LinearMap.id).range

def conormalEigenquotient := V ⧸ conormalEigenRelations d t

instance : AddCommGroup (conormalEigenquotient d t) :=
  inferInstanceAs (AddCommGroup (V ⧸ conormalEigenRelations d t))

instance : Module R (conormalEigenquotient d t) :=
  inferInstanceAs (Module R (V ⧸ conormalEigenRelations d t))

instance [Module.Finite R V] : Module.Finite R (conormalEigenquotient d t) :=
  inferInstanceAs (Module.Finite R (V ⧸ conormalEigenRelations d t))

theorem conormalEigenquotient_finitePresentation [IsNoetherianRing R] [Module.Finite R V] :
    Module.FinitePresentation R (conormalEigenquotient d t) :=
  Module.finitePresentation_of_finite R _

variable (k : Type) [CommRing k] [Algebra R k]

def conormalEigenfunctionals : Submodule k (V →ₗ[R] k) where
  carrier := {ℓ | ∀ i v, ℓ (d i v) = t i • ℓ v}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb i v
    change a (d i v) + b (d i v) = t i • (a v + b v)
    rw [ha i v, hb i v, smul_add]
  smul_mem' := by
    intro c a ha i v
    change c • a (d i v) = t i • (c • a v)
    rw [ha i v, smul_comm]

theorem mem_conormalEigenfunctionals_iff (ℓ : V →ₗ[R] k) :
    ℓ ∈ conormalEigenfunctionals d t k ↔ conormalEigenRelations d t ≤ ℓ.ker := by
  constructor
  · intro h
    apply iSup_le
    intro i v hv
    obtain ⟨w, rfl⟩ := hv
    change ℓ (d i w - t i • w) = 0
    rw [map_sub, map_smul, h i w, sub_self]
  · intro h i v
    have hle : (d i - t i • LinearMap.id).range ≤ conormalEigenRelations d t :=
      le_iSup (fun i => (d i - t i • LinearMap.id).range) i
    have hv := h (hle (LinearMap.mem_range_self (d i - t i • LinearMap.id) v))
    change ℓ (d i v - t i • v) = 0 at hv
    rw [map_sub, map_smul, sub_eq_zero] at hv
    exact hv

def quotientEigenEquiv : (conormalEigenquotient d t →ₗ[R] k) ≃ₗ[k]
    conormalEigenfunctionals d t k where
  toFun ℓ := ⟨ℓ.comp (conormalEigenRelations d t).mkQ, by
    apply (mem_conormalEigenfunctionals_iff d t k _).mpr
    intro v hv
    change ℓ ((conormalEigenRelations d t).mkQ v) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hv]
    exact ℓ.map_zero⟩
  invFun ℓ := (conormalEigenRelations d t).liftQ ℓ.val
    ((mem_conormalEigenfunctionals_iff d t k ℓ.val).mp ℓ.property)
  left_inv ℓ := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := (conormalEigenRelations d t).mkQ_surjective v
    rfl
  right_inv ℓ := by
    apply Subtype.ext
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def fiberDualEigenEquiv : Module.Dual k (k ⊗[R] conormalEigenquotient d t) ≃ₗ[k]
    conormalEigenfunctionals d t k :=
  (LinearMap.liftBaseChangeEquiv k).symm.trans (quotientEigenEquiv d t k)

theorem conormalEigenfunctionals_finrank {k : Type} [Field k] [Algebra R k]
    [Module.Finite R V] :
    Module.finrank k (conormalEigenfunctionals d t k) =
      Module.finrank k (k ⊗[R] conormalEigenquotient d t) := by
  rw [← (fiberDualEigenEquiv d t k).finrank_eq, Subspace.dual_finrank_eq]

end

/-! An actual equivariant linear comparison identifies joint Lie
eigenspaces with the coefficient fibers of the conormal eigenquotient. -/

variable {k V I : Type} [Field k] [AddCommGroup V] [Module k V]
  (T : I → Module.End k V) (c : I → k)

def jointEigenspace : Submodule k V := ⨅ i, LinearMap.ker (T i - c i • LinearMap.id)

theorem mem_jointEigenspace_iff (v : V) :
    v ∈ jointEigenspace T c ↔ ∀ i, T i v = c i • v := by
  simp only [jointEigenspace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

variable {R P : Type} [CommRing R] [Algebra R k] [AddCommGroup P] [Module R P]
  (d : I → Module.End R P) (t : I → R) (e : V ≃ₗ[k] (P →ₗ[R] k))
  (he : ∀ i v, e (T i v) = (e v).comp (d i)) (hc : ∀ i, c i = algebraMap R k (t i))

include he hc in
theorem jointEigenspace_conormal_mem_iff (v : V) :
    v ∈ jointEigenspace T c ↔ e v ∈ conormalEigenfunctionals d t k := by
  rw [mem_jointEigenspace_iff]
  have hscale (i : I) (b : P) : (c i • e v) b = t i • e v b := by
    change c i * e v b = t i • e v b
    rw [hc i]
    exact (Algebra.smul_def (t i) (e v b)).symm
  constructor
  · intro h i b
    have hv := (congrArg e (h i)).trans (e.map_smul (c i) v)
    exact (LinearMap.congr_fun (he i v) b).symm.trans
      ((LinearMap.congr_fun hv b).trans (hscale i b))
  · intro h i
    apply e.injective
    rw [e.map_smul, he i v]
    apply LinearMap.ext
    intro b
    exact (h i b).trans (hscale i b).symm

def jointConormalEquiv : jointEigenspace T c ≃ₗ[k] conormalEigenfunctionals d t k where
  toFun v := ⟨e v.val, (jointEigenspace_conormal_mem_iff T c d t e he hc v.val).mp v.property⟩
  invFun w := ⟨e.symm w.val, by
    apply (jointEigenspace_conormal_mem_iff T c d t e he hc _).mpr
    rw [e.apply_symm_apply]
    exact w.property⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.val)
  right_inv w := Subtype.ext (e.apply_symm_apply w.val)
  map_add' v w := Subtype.ext (e.map_add v.val w.val)
  map_smul' a v := Subtype.ext (e.map_smul a v.val)

include e he hc in
open scoped TensorProduct in
theorem jointEigenspace_finrank_conormal_quotient [Module.Finite R P] :
    Module.finrank k (jointEigenspace T c) =
      Module.finrank k (k ⊗[R] conormalEigenquotient d t) :=
  (jointConormalEquiv T c d t e he hc).finrank_eq.trans (conormalEigenfunctionals_finrank d t)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConormalEigenquotient

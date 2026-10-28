import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Projective Dual -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveDual.Construction.ProjectiveDualBaseChange

noncomputable section

/-! Duals of finite projective modules commute with arbitrary scalar extension. -/

open TensorProduct
open scoped TensorProduct

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (S) (M : Type u) [AddCommGroup M] [Module R M]

def map : S ⊗[R] Module.Dual R M →ₗ[S] Module.Dual S (S ⊗[R] M) :=
  (Module.Dual.baseChange S).liftBaseChange S

theorem map_tmul_tmul (a b : S) (φ : Module.Dual R M) (m : M) :
    map (R := R) S M (a ⊗ₜ[R] φ) (b ⊗ₜ[R] m) = a * (algebraMap R S (φ m) * b) := by
  simp [map, Module.Dual.baseChange_apply_tmul, Algebra.smul_def]

theorem map_tmul_one (a : S) (φ : Module.Dual R M) (m : M) :
    map (R := R) S M (a ⊗ₜ[R] φ) ((1 : S) ⊗ₜ[R] m) = a * algebraMap R S (φ m) := by
  rw [map_tmul_tmul, mul_one]

variable {M} {N : Type u} [AddCommGroup N] [Module R N]

theorem naturality (f : M →ₗ[R] N) :
    (map (R := R) S M).comp (f.dualMap.baseChange S) =
      (f.baseChange S).dualMap.comp (map (R := R) S N) := by
  apply AlgebraTensorModule.ext
  intro a φ
  apply AlgebraTensorModule.ext
  intro b m
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.dualMap_apply,
    map_tmul_tmul]

variable (M)

theorem free_bijective [Module.Free R M] [Module.Finite R M] : Function.Bijective (map (R := R) S M) := by
  let b := TensorProduct.isBaseChange R M S
  let e := b.toDualBaseChange
  have he : map (R := R) S M = e.toLinearMap := by
    apply AlgebraTensorModule.ext
    intro a φ
    apply b.algHom_ext
    intro m
    exact (map_tmul_one S M a φ m).trans (b.toDualBaseChange_tmul a φ m).symm
  rw [he]
  exact e.bijective

private theorem bijective_of_retract {A B C D : Type*} (f : A → B) (g : C → D)
    (i : A → C) (p : C → A) (j : B → D) (q : D → B)
    (hpi : ∀ x, p (i x) = x) (hqj : ∀ y, q (j y) = y)
    (hi : ∀ x, g (i x) = j (f x)) (hp : ∀ x, f (p x) = q (g x))
    (hg : Function.Bijective g) : Function.Bijective f := by
  constructor
  · intro x y h
    have h' : g (i x) = g (i y) := (hi x).trans ((congrArg j h).trans (hi y).symm)
    exact (hpi x).symm.trans ((congrArg p (hg.1 h')).trans (hpi y))
  · intro y
    obtain ⟨x, hx⟩ := hg.2 (j y)
    exact ⟨p x, (hp x).trans ((congrArg q hx).trans (hqj y))⟩

theorem bijective [Module.Projective R M] [Module.Finite R M] : Function.Bijective (map (R := R) S M) := by
  obtain ⟨n, p, i, _, _, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let a := p.dualMap.baseChange S
  let b := i.dualMap.baseChange S
  let j := (p.baseChange S).dualMap
  let q := (i.baseChange S).dualMap
  have hba : b.comp a = LinearMap.id := by
    change (i.dualMap.baseChange S).comp (p.dualMap.baseChange S) = _
    rw [← LinearMap.baseChange_comp, LinearMap.dualMap_comp_dualMap, hpi,
      LinearMap.dualMap_id, LinearMap.baseChange_id]
  have hqj : q.comp j = LinearMap.id := by
    change (i.baseChange S).dualMap.comp (p.baseChange S).dualMap = _
    rw [LinearMap.dualMap_comp_dualMap, ← LinearMap.baseChange_comp, hpi,
      LinearMap.baseChange_id, LinearMap.dualMap_id]
  exact bijective_of_retract (map (R := R) S M) (map (R := R) S (Fin n → R)) a b j q
    (fun x => LinearMap.congr_fun hba x) (fun y => LinearMap.congr_fun hqj y)
    (fun x => LinearMap.congr_fun (naturality S p) x)
    (fun x => LinearMap.congr_fun (naturality S i) x) (free_bijective S (Fin n → R))

def equiv [Module.Projective R M] [Module.Finite R M] :
    S ⊗[R] Module.Dual R M ≃ₗ[S] Module.Dual S (S ⊗[R] M) :=
  LinearEquiv.ofBijective (map (R := R) S M) (ProjectiveDualBaseChange.bijective S M)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveDual.Construction.ProjectiveDualBaseChange

import Mathlib

/-! # Exterior Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ExteriorLattice.Construction

noncomputable section

section

/-! Exterior powers of finitely generated integral modules: their
exterior products generate a finitely generated module preserved by
every linear map preserving the original module. -/

open scoped Classical TensorProduct

variable {R k V : Type*} [CommRing R] [Field k] [Algebra R k]
  [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower R k V]

def exteriorLatticeSpan (Λ : Submodule R V) (r : ℕ) : Submodule R (⋀[k]^r V) :=
  Submodule.span R (Set.range (fun v : Fin r → Λ => exteriorPower.ιMulti k r (fun i => (v i).val)))

theorem exteriorLatticeSpan_fg (Λ : Submodule R V) (hΛ : Λ.FG) (r : ℕ) :
    (exteriorLatticeSpan (k := k) Λ r).FG := by
  let : Module.Finite R Λ := Module.Finite.of_fg hΛ
  let f : MultilinearMap R (fun _ : Fin r => Λ) (⋀[k]^r V) :=
    ((exteriorPower.ιMulti k r (M := V)).toMultilinearMap.restrictScalars R).compLinearMap
      (fun _ => Λ.subtype)
  let T := PiTensorProduct.lift f
  have hrange : T.range = exteriorLatticeSpan (k := k) Λ r := by
    rw [← Submodule.map_top, ← PiTensorProduct.span_tprod_eq_top, Submodule.map_span, ← Set.range_comp]
    apply congrArg (Submodule.span R)
    apply congrArg Set.range
    funext v
    exact PiTensorProduct.lift.tprod (φ := f) v
  rw [← hrange]
  have hfg : (⊤ : Submodule R (⨂[R] (_ : Fin r), Λ)).FG := Module.Finite.fg_top
  simpa only [Submodule.map_top] using hfg.map T

theorem exteriorLatticeSpan_map_mem (Λ : Submodule R V) (r : ℕ)
    (f : V →ₗ[k] V) (hf : ∀ v ∈ Λ, f v ∈ Λ)
    {w : ⋀[k]^r V} (hw : w ∈ exteriorLatticeSpan (k := k) Λ r) :
    exteriorPower.map r f w ∈ exteriorLatticeSpan (k := k) Λ r := by
  let F := (exteriorPower.map r f).restrictScalars R
  change F w ∈ exteriorLatticeSpan (k := k) Λ r
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨v, rfl⟩ := hw
      change exteriorPower.map r f (exteriorPower.ιMulti k r (fun i => (v i).val)) ∈ _
      rw [exteriorPower.map_apply_ιMulti]
      exact Submodule.subset_span ⟨fun i => ⟨f (v i).val, hf _ (v i).property⟩, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end

/-! The exterior lattice spans the whole exterior power whenever the
original integral module spans its ambient vector space. -/

open scoped Classical TensorProduct

theorem exteriorLatticeSpan_full
    {R k V : Type*} [CommRing R] [Field k] [Algebra R k]
    [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower R k V]
    (Λ : Submodule R V) (hΛ : Submodule.span k (Λ : Set V) = ⊤) (r : ℕ) :
    Submodule.span k (exteriorLatticeSpan (k := k) Λ r : Set (⋀[k]^r V)) = ⊤ := by
  let M := Submodule.span k (exteriorLatticeSpan (k := k) Λ r : Set (⋀[k]^r V))
  let i : (⋀[k]^r V) →ₗ[k] ExteriorAlgebra k V := (⋀[k]^r V).subtype
  have hfull : (⋀[k]^r V) ≤ M.map i := by
    conv_lhs => rw [← exteriorPower.ιMulti_span_fixedDegree_of_span_eq_top (R := k) (n := r) V hΛ]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    let u : Fin r → Λ := fun j => ⟨v j, hv (Set.mem_range_self j)⟩
    refine ⟨exteriorPower.ιMulti k r (fun j => (u j).val), ?_, rfl⟩
    exact Submodule.subset_span (Submodule.subset_span (Set.mem_range_self u))
  apply top_unique
  intro w _
  obtain ⟨z, hz, he⟩ := hfull w.property
  have hzEq : z = w := Subtype.ext he
  exact hzEq ▸ hz

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ExteriorLattice.Construction

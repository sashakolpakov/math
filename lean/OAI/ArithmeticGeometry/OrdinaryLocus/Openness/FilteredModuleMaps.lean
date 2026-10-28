import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredModuleFg
import Mathlib.RingTheory.Finiteness.Basic

/-! # Filtered Module Maps -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredModuleMaps.Construction

noncomputable section

/-! Finite generating subspaces give uniformly bounded shifts for actual module maps. -/

variable {K B σ M N : Type*} [Field K] [CommRing B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module B M] [IsScalarTower K B M]
    [AddCommGroup N] [Module K N] [Module B N] [IsScalarTower K B N]

theorem finiteModuleSubmodule_bounded_in_exhaustive_filtration
    (F : ℕ → Submodule K N) (hF : Monotone F) (hex : ∀ x : N, ∃ n, x ∈ F n)
    (W : Submodule K N) (hW : W.FG) : ∃ n : ℕ, W ≤ F n := by
  classical
  obtain ⟨s, hs⟩ := hW
  choose b hb using fun x : s => hex x.1
  refine ⟨s.attach.sup b, ?_⟩
  rw [← hs, Submodule.span_le]
  intro x hx
  exact hF (Finset.le_sup (f := b) (s.mem_attach ⟨x, hx⟩)) (hb ⟨x, hx⟩)

theorem exists_polynomialFilteredModule_map_shift (v : σ → B)
    (hv : Algebra.adjoin K (Set.range v) = ⊤)
    (T : Submodule K M) (hT : T.FG) (S : Submodule K N)
    (hS : Submodule.span B (S : Set N) = ⊤) (f : M →ₗ[B] N) :
    ∃ c : ℕ, ∀ n : ℕ, (FilteredModuleFg.Construction.polynomialFilteredModule v T n).map (f.restrictScalars K) ≤
      FilteredModuleFg.Construction.polynomialFilteredModule v S (n + c) := by
  obtain ⟨c, hc⟩ := finiteModuleSubmodule_bounded_in_exhaustive_filtration
    (FilteredModuleFg.Construction.polynomialFilteredModule v S) (FilteredModuleFg.Construction.polynomialFilteredModule_mono v S)
    (FilteredModuleFg.Construction.polynomialFilteredModule_exhaustive v hv S hS)
    (T.map (f.restrictScalars K)) (hT.map _)
  exact ⟨c, fun n => FilteredModuleFg.Construction.polynomialFilteredModule_map_shift v T S f c
    (fun x hx => hc ⟨x, hx, rfl⟩) n⟩

def filteredModuleMap (v : σ → B) (T : Submodule K M) (S : Submodule K N)
    (f : M →ₗ[B] N) (n m : ℕ)
    (h : (FilteredModuleFg.Construction.polynomialFilteredModule v T n).map (f.restrictScalars K) ≤ FilteredModuleFg.Construction.polynomialFilteredModule v S m) :
    FilteredModuleFg.Construction.polynomialFilteredModule v T n →ₗ[K] FilteredModuleFg.Construction.polynomialFilteredModule v S m :=
  ((f.restrictScalars K).domRestrict (FilteredModuleFg.Construction.polynomialFilteredModule v T n)).codRestrict _
    (fun x => h ⟨x.val, x.property, rfl⟩)

theorem filteredModuleMap_injective (v : σ → B) (T : Submodule K M) (S : Submodule K N)
    (f : M →ₗ[B] N) (hf : Function.Injective f) (n m : ℕ)
    (h : (FilteredModuleFg.Construction.polynomialFilteredModule v T n).map (f.restrictScalars K) ≤ FilteredModuleFg.Construction.polynomialFilteredModule v S m) :
    Function.Injective (filteredModuleMap v T S f n m h) := by
  intro x y hxy
  apply Subtype.ext
  exact hf (congrArg Subtype.val hxy)

theorem filteredModuleMap_finrank_le (v : σ → B) (T : Submodule K M) (S : Submodule K N)
    (f : M →ₗ[B] N) (hf : Function.Injective f) (n m : ℕ)
    [Module.Finite K (FilteredModuleFg.Construction.polynomialFilteredModule v S m)]
    (h : (FilteredModuleFg.Construction.polynomialFilteredModule v T n).map (f.restrictScalars K) ≤ FilteredModuleFg.Construction.polynomialFilteredModule v S m) :
    Module.finrank K (FilteredModuleFg.Construction.polynomialFilteredModule v T n) ≤ Module.finrank K (FilteredModuleFg.Construction.polynomialFilteredModule v S m) :=
  LinearMap.finrank_le_finrank_of_injective (filteredModuleMap_injective v T S f hf n m h)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredModuleMaps.Construction

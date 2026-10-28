import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutRows
import OAI.Algorithms.SubexponentialSAT.SubexpMainCacheBounds

namespace OAI.Algorithms

/-!
# Retained data after the actual cache-and-row suffix

The actual cache producer bounds all seven persistent cache words. The
Lagrange and row programs preserve those words, parameters and thresholds,
so the same bound can be reused for every sparse leaf.
-/

namespace SubexponentialSAT.SubexpMainLayoutInvariant

open SubexpMainProgram SubexpSetupProgram SubexpMainInvariant
open SubexpLayoutPorts (Allocation)
open Subexp.ConstructivePacking

theorem parameter_not_changed (i : Fin 32) (hi : ParameterPort i) :
    i ∉ SubexpMainCacheSetup.changedPersistent := by
  intro h
  simp only [SubexpMainCacheSetup.changedPersistent, List.mem_cons,
    List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [ParameterPort, Fin.coe_ofNat_eq_mod] at hi

variable {p r Δ D : ℕ} [Fact p.Prime]
  (xs : List (ZMod p))
  (P : PackingData (Fin D) (MulticolorTypes.UniversalType r (p^4 - 1) Δ))
  (scopes : List (List ℕ))
  (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)

theorem after_cache_words {er es : ℕ} {hr : 16 ≤ er} {alloc : Allocation es}
    {a out : MainState er es}
    (h : SubexpMainLayoutRows.Result xs P scopes hd hr alloc a out) (i : Fin 32) :
    out.stacks (SubexpMainProgram.persistent es i) =
      h.afterCache.stacks (SubexpMainProgram.persistent es i) :=
  (SubexpMainRows.Result.persistent_frame h.cacheFacts.source xs h.cacheFacts.inverse
    h.cacheFacts.negative h.cacheFacts.difference P scopes hd h.rows i).trans
    (h.lagrange.persistent i)

theorem thresholds {er es : ℕ} {hr : 16 ≤ er} {alloc : Allocation es}
    {a out : MainState er es}
    (h : SubexpMainLayoutRows.Result xs P scopes hd hr alloc a out)
    (i : Fin (totalStacks es)) (hlo : alloc.ordinaryCount ≤ i.val)
    (hhi : i.val < workStacks es) : out.stacks i = a.stacks i := by
  have hi : 672 ≤ i.val := alloc.enough.trans hlo
  exact (SubexpMainRows.Result.threshold_frame h.cacheFacts.source xs h.cacheFacts.inverse
    h.cacheFacts.negative h.cacheFacts.difference P scopes hd h.rows i hlo hhi).trans
    ((h.lagrange.work_frame i hhi (Or.inr (by omega)) (by omega)).trans
      (h.cache.work_frame i (by omega) (Or.inr (by omega)) (by omega) hhi))

theorem stored {cfg : Config} {er : ℕ} {hr : 16 ≤ er}
    {alloc : Allocation (mainExtraStacks cfg)} {a out : MainState er (mainExtraStacks cfg)}
    (h : SubexpMainLayoutRows.Result xs P scopes hd hr alloc a out)
    (halloc : alloc.ordinaryCount = helperSize cfg)
    {setup : SetupState cfg} {B : ℕ}
    (initial : Stored cfg setup B a)
    (hB : SubexpMainCacheBounds.regeneratedBound p D ≤ B) :
    Stored cfg setup B out := by
  apply stored_of_frames initial
  · intro i hi
    exact SubexpMainLayoutRows.Result.persistent_frame xs P scopes hd h i
      (parameter_not_changed i hi)
  · intro i
    have hithreshold := threshold_range cfg i
    apply thresholds xs P scopes hd h _ _ hithreshold.2
    rw [halloc]
    exact hithreshold.1
  · intro i hi
    rw [after_cache_words xs P scopes hd h i]
    exact SubexpMainCacheBounds.setup_caches h.cache B hB i hi

end SubexponentialSAT.SubexpMainLayoutInvariant

end OAI.Algorithms

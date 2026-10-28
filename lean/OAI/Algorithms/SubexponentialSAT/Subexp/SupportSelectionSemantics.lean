import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.SupportSelectionData
import OAI.Algorithms.SubexponentialSAT.Subexp.ComputedLayout

namespace OAI.Algorithms

/-!
# The physical support-selection lists are the layout supports

The selector scans numeric ambient coordinates. These lemmas identify its
actual lookup/head-color tests with the packed support sets, and identify
its ascending outside list with the packing's original-order leftovers.
-/

namespace SubexponentialSAT.Subexp.SupportSelectionSemantics

open MulticolorTypes ConstructivePacking SupportSelectionProgram

variable {D r Q Δ : ℕ}
variable (P : PackingData (Fin D) (UniversalType r Q Δ))

theorem colorAt_eq_supportAt (t : Fin Q) (g : Fin r) (v : Fin D) :
    colorAt P t g.val v = ComputedLayout.supportAt P (side (Δ := Δ) t g).toFinset v := by
  cases h : P.lookup v with
  | none => simp [colorAt, ComputedLayout.supportAt, h]
  | some z =>
    simp [colorAt, ComputedLayout.supportAt, h, mem_side, Fin.val_inj]

theorem colorAt_true_iff (t : Fin Q) (g : Fin r) (v : Fin D) :
    colorAt P t g.val v = true ↔
      v ∈ DirectSums.packedSupportFinset P.completeBlocks.embed (side (Δ := Δ) t g).toFinset := by
  rw [colorAt_eq_supportAt]
  exact ComputedLayout.supportAt_iff P _ v

theorem outsideAt_true_iff (v : Fin D) :
    outsideAt P v = true ↔ v ∉ Set.range P.completeBlocks.embed := by
  rw [← P.lookup_none_iff]
  cases h : P.lookup v <;> simp [outsideAt, h]

theorem unary_injective : Function.Injective unary := by
  intro a b h
  simpa only [List.length_replicate] using congrArg List.length h

theorem mem_indexWords (test : ℕ → Bool) (N n : ℕ) :
    unary n ∈ indexWords test N ↔ n < N ∧ test n = true := by
  rw [indexWords, List.mem_map]
  constructor
  · rintro ⟨m, hm, he⟩
    have hmn := unary_injective he
    subst m
    simpa only [List.mem_filter, List.mem_range] using hm
  · intro hn
    exact ⟨n, by simpa only [List.mem_filter, List.mem_range] using hn, rfl⟩

theorem indexWords_nodup (test : ℕ → Bool) (N : ℕ) :
    (indexWords test N).Nodup :=
  ((show (List.range N).Nodup from List.nodup_range).filter test).map unary_injective

theorem color_indexWords_mem_iff (t : Fin Q) (g : Fin r) (v : Fin D) :
    unary v.val ∈ indexWords (colorTest P t g.val) D ↔
      v ∈ DirectSums.packedSupportFinset P.completeBlocks.embed (side (Δ := Δ) t g).toFinset := by
  rw [mem_indexWords]
  simpa only [colorTest, v.isLt, dite_true, true_and] using colorAt_true_iff P t g v

theorem outside_indexWords_mem_iff (v : Fin D) :
    unary v.val ∈ indexWords (outsideTest P) D ↔
      v ∉ Set.range P.completeBlocks.embed := by
  rw [mem_indexWords]
  simpa only [outsideTest, v.isLt, dite_true, true_and] using outsideAt_true_iff P v

/-- This is the selector's literal ascending order, not just a set equality. -/
theorem color_indexWords (t : Fin Q) (g : Fin r) :
    indexWords (colorTest P t g.val) D =
      ((List.finRange D).filter (colorAt P t g.val)).map (fun v => unary v.val) := by
  have hfilter : (List.range D).filter (colorTest P t g.val) =
      ((List.finRange D).filter (colorAt P t g.val)).map Fin.val := by
    rw [← List.map_coe_finRange D, List.filter_map]
    simp only [Function.comp_def, colorTest, Fin.isLt, dite_true]
  rw [indexWords, hfilter, List.map_map]
  rfl

/-- On the actual numeric packing input, the outside selector emits exactly
the leftover list used by the global outer columns. -/
theorem outside_indexWords_eq_leftovers
    (hvertices : P.vertices.values = List.finRange D) :
    indexWords (outsideTest P) D = P.leftovers.map (fun v => unary v.val) := by
  have hleft : P.leftovers = (List.finRange D).filter (outsideAt P) := by
    unfold PackingData.leftovers
    rw [hvertices]
    congr 1
    funext v
    cases h : P.lookup v <;> simp [outsideAt, h]
  have hfilter : (List.range D).filter (outsideTest P) =
      ((List.finRange D).filter (outsideAt P)).map Fin.val := by
    rw [← List.map_coe_finRange D, List.filter_map]
    simp only [Function.comp_def, outsideTest, Fin.isLt, dite_true]
  rw [indexWords, hfilter, List.map_map, hleft]
  rfl

end SubexponentialSAT.Subexp.SupportSelectionSemantics

end OAI.Algorithms

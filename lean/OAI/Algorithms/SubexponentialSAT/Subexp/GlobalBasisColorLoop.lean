import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisExecution

namespace OAI.Algorithms

/-! The actual descending color loop emits the inner matrix records in
ascending color order by prepending each freshly computed record. -/

namespace SubexponentialSAT.Subexp.GlobalBasisProgram

open BitProgram StructuredCalls
open GlobalBasisInput (Context Location)

def innerWordAt {p r Q Δ : ℕ} (C : Context p r Q Δ) (count : ℕ)
    (locs : List (Location r Q Δ)) (g : ℕ) : List Bool :=
  if hg : g < r then innerRecord C count locs ⟨g, hg⟩ else []

def innerCostAt {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ) (count : ℕ)
    (locs : List (Location r Q Δ)) (g : ℕ) : ℕ :=
  if hg : g < r then innerStepBudget C count locs ⟨g, hg⟩ else 0

def innerPrefix {p r Q Δ : ℕ} (C : Context p r Q Δ) (count : ℕ)
    (locs : List (Location r Q Δ)) (colors : ℕ) : List Bool :=
  (List.range colors).flatMap (innerWordAt C count locs)

theorem innerPrefix_succ {p r Q Δ : ℕ} (C : Context p r Q Δ) (count : ℕ)
    (locs : List (Location r Q Δ)) (colors : ℕ) :
    innerPrefix C count locs (colors+1) = innerPrefix C count locs colors ++ innerWordAt C count locs colors := by
  simp [innerPrefix, List.range_succ]

def colorBudget {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ) (count : ℕ)
    (locs : List (Location r Q Δ)) : ℕ → ℕ
  | 0 => 2
  | colors+1 => innerCostAt C count locs colors + colorBudget C count locs colors + 2

theorem stored_color_frame {p r Q Δ : ℕ} [Fact p.Prime] {C : Context p r Q Δ} {d e : Data}
    (h : C.Stored d) (counter output : List Bool)
    (hs : e.stacks = Function.update (Function.update d.stacks 55 counter) 63 output) : C.Stored e := by
  constructor
  · simpa [hs] using h.width
  · simpa [hs] using h.zero
  · simpa [hs] using h.one
  · simpa [hs] using h.position
  · simpa [hs] using h.metadata
  · simpa [hs] using h.universal
  · simpa [hs] using h.colors
  · simpa [hs] using h.batch

theorem clean_color_frame {d e : Data} (h : WorkClean d) (counter output : List Bool)
    (hs : e.stacks = Function.update (Function.update d.stacks 55 counter) 63 output) : WorkClean e := by
  intro i hi
  have h55 : i ≠ 55 := by intro he; subst i; exact hi (by decide)
  have h63 : i ≠ 63 := by intro he; subst i; exact hi (by decide)
  simpa [hs, h55, h63] using h i hi

theorem color_visits {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ) (count : ℕ)
    (locs : List (Location r Q Δ)) (colors : ℕ) :
    ∀ (d : Data), colors ≤ r → C.locations 0 locs → C.Stored d → WorkClean d →
      d.stacks 46 = List.replicate locs.length true → d.stacks 48 = List.replicate count true →
      d.stacks 55 = List.replicate colors true →
      (∀ g : Fin r, ∀ loc ∈ locs, ∀ x ∈ innerColumns C count g, GlobalBasisEntry.Valid (C.row loc) x) →
      ∃ costs n e, n ≤ colorBudget C count locs colors ∧
        UnaryForPrograms.Visits colorPorts innerStep costs n d e ∧
        e.stacks = Function.update (Function.update d.stacks 55 []) 63
          (innerPrefix C count locs colors ++ d.stacks 63) := by
  induction colors with
  | zero =>
    intro d hr hm hs hc h46 h48 h55 hv
    refine ⟨[], 2, UnaryForPrograms.popped colorPorts d, by rfl,
      .done d (by simpa [colorPorts] using h55), ?_⟩
    funext i
    by_cases h55' : i = 55 <;> by_cases h63 : i = 63 <;>
      simp_all [UnaryForPrograms.popped, colorPorts, innerPrefix]
  | succ colors ih =>
    intro d hr hm hs hc h46 h48 h55 hv
    have hlt : colors < r := by omega
    let g : Fin r := ⟨colors, hlt⟩
    let a := UnaryForPrograms.popped colorPorts d
    have has : a.stacks = Function.update d.stacks 55 (List.replicate colors true) := by
      simp [a, UnaryForPrograms.popped, colorPorts, h55, List.replicate_succ]
    have hastored : C.Stored a := stored_color_frame hs _ _ (by
      rw [has]
      exact (Function.update_eq_self 63 _).symm)
    have haclean : WorkClean a := clean_color_frame hc _ _ (by
      rw [has]
      exact (Function.update_eq_self 63 _).symm)
    obtain ⟨n₁, b, hn₁, hb, hsb⟩ := innerStep_eval C count locs g a hm hastored haclean
      (by simp [has, h46]) (by simp [has, h48]) (by simp [has, g]) (hv g)
    have hbframe : b.stacks = Function.update (Function.update d.stacks 55 (List.replicate colors true)) 63
        (innerRecord C count locs g ++ d.stacks 63) := by simp [hsb, has]
    obtain ⟨costs, n₂, e, hn₂, he, hse⟩ := ih b (by omega) hm
      (stored_color_frame hs _ _ hbframe) (clean_color_frame hc _ _ hbframe)
      (by simp [hbframe, h46]) (by simp [hbframe, h48]) (by simp [hbframe]) hv
    refine ⟨n₁ :: costs, n₁+n₂+2, e, ?_,
      .step (by simp [colorPorts, h55, List.replicate_succ]) hb (by simp [hsb, colorPorts, a]) he, ?_⟩
    · simp only [colorBudget, innerCostAt, dite_eq_left hlt]
      change n₁ + n₂ + 2 ≤ innerStepBudget C count locs g + colorBudget C count locs colors + 2
      omega
    · rw [hse, hbframe]
      funext i
      by_cases h55' : i = 55 <;> by_cases h63 : i = 63 <;>
        simp_all [innerPrefix_succ, innerWordAt, g, List.append_assoc]

theorem innerMatrices_eval {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ) (count : ℕ)
    (locs : List (Location r Q Δ)) (d : Data)
    (hm : C.locations 0 locs) (hs : C.Stored d) (hc : WorkClean d)
    (h46 : d.stacks 46 = List.replicate locs.length true) (h48 : d.stacks 48 = List.replicate count true)
    (h55 : d.stacks 55 = List.replicate r true)
    (hv : ∀ g : Fin r, ∀ loc ∈ locs, ∀ x ∈ innerColumns C count g, GlobalBasisEntry.Valid (C.row loc) x) :
    ∃ n e, n ≤ colorBudget C count locs r ∧ Eval innerMatrices n d e ∧
      e.stacks = Function.update (Function.update d.stacks 55 []) 63
        (innerPrefix C count locs r ++ d.stacks 63) := by
  obtain ⟨costs, n, e, hn, he, hse⟩ := color_visits C count locs r d le_rfl hm hs hc h46 h48 h55 hv
  exact ⟨n, e, hn, he.eval, hse⟩

end SubexponentialSAT.Subexp.GlobalBasisProgram

end OAI.Algorithms

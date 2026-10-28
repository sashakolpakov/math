import OAI.Analysis.PDE.Elliptic.Boundary.Slope

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def boundaryQuotientSet (v : E) (u : E → ℝ) (r : ℝ) : Set ℝ :=
  (fun x => u x / inner ℝ v x) '' {x | ‖x‖ ≤ r ∧ 0 < inner ℝ v x}

def boundarySlopeInf (v : E) (u : E → ℝ) (r : ℝ) : ℝ := sInf (boundaryQuotientSet v u r)
def boundarySlopeSup (v : E) (u : E → ℝ) (r : ℝ) : ℝ := sSup (boundaryQuotientSet v u r)
def boundarySlopeOsc (v : E) (u : E → ℝ) (r : ℝ) : ℝ :=
  boundarySlopeSup v u r - boundarySlopeInf v u r

theorem boundaryQuotientSet_nonempty (v : E) (hv : ‖v‖ = 1) (u : E → ℝ)
    {r : ℝ} (hr : 0 < r) : (boundaryQuotientSet v u r).Nonempty := by
  refine ⟨u (r • v) / inner ℝ v (r • v), r • v, ?_, rfl⟩
  constructor
  · simp [norm_smul, hv, abs_of_pos hr]
  · simpa [real_inner_smul_right, hv] using hr

theorem boundaryQuotientSet_mono (v : E) (u : E → ℝ) {r R : ℝ} (hrR : r ≤ R) :
    boundaryQuotientSet v u r ⊆ boundaryQuotientSet v u R := by
  rintro t ⟨x, hx, rfl⟩
  exact ⟨x, ⟨hx.1.trans hrR, hx.2⟩, rfl⟩

theorem boundaryQuotientSet_bounds (v : E) (u : E → ℝ) {r m M : ℝ}
    (hb : ∀ x, ‖x‖ ≤ r → 0 ≤ inner ℝ v x →
      m * inner ℝ v x ≤ u x ∧ u x ≤ M * inner ℝ v x) :
    ∀ t ∈ boundaryQuotientSet v u r, m ≤ t ∧ t ≤ M := by
  rintro t ⟨x, hx, rfl⟩
  have h := hb x hx.1 hx.2.le
  exact ⟨(le_div_iff₀ hx.2).mpr h.1, (div_le_iff₀ hx.2).mpr h.2⟩

theorem boundarySlope_extrema_bounds (v : E) (hv : ‖v‖ = 1) (u : E → ℝ)
    {r m M : ℝ} (hr : 0 < r)
    (hb : ∀ x, ‖x‖ ≤ r → 0 ≤ inner ℝ v x →
      m * inner ℝ v x ≤ u x ∧ u x ≤ M * inner ℝ v x) :
    m ≤ boundarySlopeInf v u r ∧ boundarySlopeInf v u r ≤ boundarySlopeSup v u r ∧
      boundarySlopeSup v u r ≤ M := by
  have hne := boundaryQuotientSet_nonempty v hv u hr
  have hs := boundaryQuotientSet_bounds v u hb
  have hbelow : BddBelow (boundaryQuotientSet v u r) := ⟨m, fun t ht => (hs t ht).1⟩
  have habove : BddAbove (boundaryQuotientSet v u r) := ⟨M, fun t ht => (hs t ht).2⟩
  refine ⟨le_csInf hne (fun t ht => (hs t ht).1), ?_, csSup_le hne (fun t ht => (hs t ht).2)⟩
  obtain ⟨t, ht⟩ := hne
  exact (csInf_le hbelow ht).trans (le_csSup habove ht)

theorem boundarySlope_pointwise_bounds (v : E) (u : E → ℝ)
    {r m M : ℝ}
    (hb : ∀ x, ‖x‖ ≤ r → 0 ≤ inner ℝ v x →
      m * inner ℝ v x ≤ u x ∧ u x ≤ M * inner ℝ v x) :
    ∀ x, ‖x‖ ≤ r → 0 ≤ inner ℝ v x →
      boundarySlopeInf v u r * inner ℝ v x ≤ u x ∧
        u x ≤ boundarySlopeSup v u r * inner ℝ v x := by
  have hs := boundaryQuotientSet_bounds v u hb
  have hbelow : BddBelow (boundaryQuotientSet v u r) := ⟨m, fun t ht => (hs t ht).1⟩
  have habove : BddAbove (boundaryQuotientSet v u r) := ⟨M, fun t ht => (hs t ht).2⟩
  intro x hx ht
  obtain he | he := ht.eq_or_lt
  · have hh := hb x hx ht
    simp only [← he, mul_zero] at hh ⊢
    exact hh
  · have hm : u x / inner ℝ v x ∈ boundaryQuotientSet v u r := ⟨x, ⟨hx, he⟩, rfl⟩
    exact ⟨(le_div_iff₀ he).mp (csInf_le hbelow hm), (div_le_iff₀ he).mp (le_csSup habove hm)⟩

theorem boundarySlopeOsc_mono (v : E) (hv : ‖v‖ = 1) (u : E → ℝ)
    {r R m M : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hb : ∀ x, ‖x‖ ≤ R → 0 ≤ inner ℝ v x →
      m * inner ℝ v x ≤ u x ∧ u x ≤ M * inner ℝ v x) :
    boundarySlopeOsc v u r ≤ boundarySlopeOsc v u R := by
  have hne := boundaryQuotientSet_nonempty v hv u hr
  have hs := boundaryQuotientSet_bounds v u hb
  have hbelow : BddBelow (boundaryQuotientSet v u R) := ⟨m, fun t ht => (hs t ht).1⟩
  have habove : BddAbove (boundaryQuotientSet v u R) := ⟨M, fun t ht => (hs t ht).2⟩
  have hsub := boundaryQuotientSet_mono v u hrR
  have hsup : boundarySlopeSup v u r ≤ boundarySlopeSup v u R :=
    csSup_le hne (fun t ht => le_csSup habove (hsub ht))
  have hinf : boundarySlopeInf v u R ≤ boundarySlopeInf v u r :=
    le_csInf hne (fun t ht => csInf_le hbelow (hsub ht))
  exact sub_le_sub hsup hinf

end OAI.Analysis.PDE.Elliptic

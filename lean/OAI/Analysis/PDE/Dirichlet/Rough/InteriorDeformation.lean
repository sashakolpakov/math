import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.ChartShift

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.SmoothExtension

variable {E T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [AddCommGroup T]

omit [FiniteDimensional ℝ E] [Nontrivial E] [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem mem_iff_of_injective_eq_self_off {F : E → E} (hi : Function.Injective F)
    {S : Set E} (hoff : ∀ x ∉ S, F x = x) (x : E) : F x ∈ S ↔ x ∈ S := by
  constructor
  · intro hx
    by_contra hn
    exact hn (by simpa only [hoff x hn] using hx)
  · intro hx
    exact mapsTo_of_injective_eq_self_off hi hoff hx

/-- Genuine periodic translations near an interior point, obtained by
periodizing a compact smooth cutoff. The family fixes the complement of
the domain, so bijectivity proves exact domain preservation. -/
theorem exists_periodic_interior_shift
    (L : T →+ E) (hLi : Function.Injective L)
    (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    (S : Set E) (hS : IsOpen S) (hSp : ∀ x z, x + L z ∈ S ↔ x ∈ S)
    {a : E} (ha : a ∈ S) (v : E) :
    ∃ Φ : ℝ × E → E, ∃ d : ℝ, 0 < d ∧ ContDiff ℝ ∞ Φ ∧
      (∀ x, Φ (0,x) = x) ∧
      (∀ t : ℝ, |t| < d → Function.Bijective (fun x ↦ Φ (t,x))) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ Function.invFun (fun x ↦ Φ (p.1,x)) p.2)
        {p | |p.1| < d} ∧
      (∀ t x z, Φ (t,x + L z) = Φ (t,x) + L z) ∧
      (∀ t x, x ∉ S → Φ (t,x) = x) ∧
      (∀ t : ℝ, |t| < d → ∀ x, Φ (t,x) ∈ S ↔ x ∈ S) ∧
      ((fun p : ℝ × E ↦ Φ p) =ᶠ[𝓝 (0,a)] (fun p ↦ p.2 + p.1 • v)) := by
  classical
  obtain ⟨ε,hε,hεS⟩ := Metric.isOpen_iff.mp hS a ha
  obtain ⟨gap,hgap,hgapL⟩ := OAI.Analysis.Calculus.SmoothExtension.exists_positive_period_gap L hLi hL
  let R : ℝ := min (ε/2) (gap/4)
  have hR : 0 < R := lt_min (by positivity) (by positivity)
  have hRε : R < ε := (min_le_left _ _).trans_lt (by linarith)
  have hRg : 2 * R < gap := by have := min_le_right (ε/2) (gap/4); dsimp [R]; linarith
  let K : Set E := closedBall a R
  have hK : IsCompact K := isCompact_closedBall a R
  have hKS : K ⊆ S := by
    intro x hx
    exact hεS (lt_of_le_of_lt hx hRε)
  have hdis : ∀ x z w, x + L z ∈ K → x + L w ∈ K → z = w :=
    disjoint_period_translates_of_radius L hgapL hRg a
  let b : ContDiffBump a := ⟨R/2,R,by positivity,by linarith⟩
  let h : ℝ × E → E := fun p ↦ p.1 • (b p.2 • v)
  have hh : ContDiff ℝ ∞ h := contDiff_fst.smul ((b.contDiff.comp contDiff_snd).smul contDiff_const)
  have hs (t : ℝ) (x : E) (hx : x ∉ K) : h (t,x) = 0 := by
    have hxb : b x = 0 := b.zero_of_le_dist (le_of_not_ge hx)
    simp only [h,hxb,zero_smul,smul_zero]
  have hz (x : E) : h (0,x) = 0 := by simp [h]
  obtain ⟨d,hd,hbij,hi⟩ := exists_smooth_periodic_deformation_inverse L hL hK hdis h hh hs hz
  let Φ : ℝ × E → E := fun p ↦ periodicPerturbation L (fun x ↦ h (p.1,x)) p.2
  have hΦ : ContDiff ℝ ∞ Φ :=
    contDiff_snd.add (contDiff_parametricPeriodization L hL hK h hs hh)
  have hoff (t : ℝ) (x : E) (hx : x ∉ S) : Φ (t,x) = x := by
    apply periodicPerturbation_eq_self L _ (hs t) x
    intro z hz
    exact hx ((hSp x z).mp (hKS hz))
  refine ⟨Φ,d,hd,hΦ,?_,hbij,hi,?_,hoff,?_,?_⟩
  · intro x
    change x + (∑' z, h (0,x + L z)) = x
    simp only [hz,tsum_zero,add_zero]
  · intro t x z
    exact periodicPerturbation_add L _ z x
  · intro t ht x
    exact mem_iff_of_injective_eq_self_off (hbij t ht).injective (hoff t) x
  · have hb : closedBall a (R/2) ∈ 𝓝 a := closedBall_mem_nhds a (by positivity)
    filter_upwards [(continuous_snd.tendsto ((0 : ℝ),a)).eventually hb] with p hp
    have hpK : p.2 ∈ K := le_trans hp (by linarith)
    have he := periodicPerturbation_at L (fun x ↦ h (p.1,x)) (hs p.1) hdis p.2 0
      (by simpa only [map_zero,add_zero] using hpK)
    change periodicPerturbation L (fun x ↦ h (p.1,x)) p.2 = _
    rw [he]
    simp only [map_zero,add_zero,h,b.one_of_mem_closedBall hp,one_smul]

/-- Specialization to a periodic sublevel. Both the open domain and its
closed counterpart are preserved, while the entire nonnegative side is
fixed pointwise. The defining function itself need not be invariant. -/
theorem exists_periodic_sublevel_interior_shift
    (L : T →+ E) (hLi : Function.Injective L)
    (hL : ∀ R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    (r : E → ℝ) (hr : Continuous r) (hrp : ∀ x z, r (x + L z) = r x)
    {a : E} (ha : r a < 0) (v : E) :
    ∃ Φ : ℝ × E → E, ∃ d : ℝ, 0 < d ∧ ContDiff ℝ ∞ Φ ∧
      (∀ x, Φ (0,x) = x) ∧
      (∀ t : ℝ, |t| < d → Function.Bijective (fun x ↦ Φ (t,x))) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ Function.invFun (fun x ↦ Φ (p.1,x)) p.2)
        {p | |p.1| < d} ∧
      (∀ t x z, Φ (t,x + L z) = Φ (t,x) + L z) ∧
      (∀ t x, 0 ≤ r x → Φ (t,x) = x) ∧
      (∀ t : ℝ, |t| < d → ∀ x,
        (r (Φ (t,x)) < 0 ↔ r x < 0) ∧ (r (Φ (t,x)) ≤ 0 ↔ r x ≤ 0)) ∧
      ((fun p : ℝ × E ↦ Φ p) =ᶠ[𝓝 (0,a)] (fun p ↦ p.2 + p.1 • v)) := by
  obtain ⟨Φ,d,hd,hΦ,hzero,hbij,hi,hper,hoff,hdom,hgerm⟩ :=
    exists_periodic_interior_shift L hLi hL {x | r x < 0}
      (isOpen_lt hr continuous_const) (by intro x z; simp only [Set.mem_ofPred_eq,hrp x z]) ha v
  refine ⟨Φ,d,hd,hΦ,hzero,hbij,hi,hper,?_,?_,hgerm⟩
  · intro t x hx
    exact hoff t x (not_lt.mpr hx)
  · intro t ht x
    have hlt : r (Φ (t,x)) < 0 ↔ r x < 0 := hdom t ht x
    refine ⟨hlt,?_⟩
    by_cases hx : r x < 0
    · exact ⟨fun _ ↦ hx.le,fun _ ↦ (hlt.mpr hx).le⟩
    · rw [hoff t x hx]

end OAI.Analysis.PDE.Dirichlet

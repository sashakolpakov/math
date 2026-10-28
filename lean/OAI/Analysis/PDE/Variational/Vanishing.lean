import OAI.Analysis.PDE.Variational.PeriodicH1Equation

open Set Filter _root_.MeasureTheory
noncomputable section
namespace OAI.Analysis.PDE.Variational

section General
variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {μ : Measure X}

def outsideCoefficient (Ω : Set X) (x : X) : H →L[ℝ] H := by
  classical
  exact if x∈Ω then 0 else ContinuousLinearMap.id ℝ H

theorem outsideCoefficient_measurable {Ω : Set X} (hΩ : MeasurableSet Ω) :
    AEStronglyMeasurable (outsideCoefficient (H:=H) Ω) μ := by
  classical
  exact aestronglyMeasurable_const.piecewise hΩ aestronglyMeasurable_const

omit [MeasurableSpace X] in
theorem outsideCoefficient_bound (Ω : Set X) (x : X) :
    ‖outsideCoefficient (H:=H) Ω x‖≤1 := by
  classical
  unfold outsideCoefficient
  split_ifs
  · simp
  · exact ContinuousLinearMap.norm_id_le

def outsideL2 (Ω : Set X) (hΩ : MeasurableSet Ω) : Lp H 2 μ →L[ℝ] Lp H 2 μ :=
  OAI.Analysis.PDE.Dirichlet.coefficientLpCLM (outsideCoefficient Ω) (outsideCoefficient_measurable hΩ)
    zero_le_one (Eventually.of_forall (outsideCoefficient_bound Ω))

theorem outsideL2_eq_zero_iff (Ω : Set X) (hΩ : MeasurableSet Ω) (f : Lp H 2 μ) :
    outsideL2 Ω hΩ f=0 ↔ ∀ᵐ x ∂μ, x∉Ω → f x=0 := by
  classical
  have hae := OAI.Analysis.PDE.Dirichlet.coefficientLpCLM_ae (outsideCoefficient Ω)
    (outsideCoefficient_measurable hΩ) zero_le_one
    (Eventually.of_forall (outsideCoefficient_bound Ω)) f
  constructor
  · intro hf
    change outsideL2 Ω hΩ f =ᵐ[μ] _ at hae
    rw [hf] at hae
    filter_upwards [hae,Lp.coeFn_zero H 2 μ] with x hx hz
    intro hxo
    have hz' : (0 : Lp H 2 μ) x=0 := hz
    rw [hz'] at hx
    simpa [outsideCoefficient,hxo] using hx.symm
  · intro hf
    apply Lp.ext
    filter_upwards [hae,hf,Lp.coeFn_zero H 2 μ] with x hx hy hz
    rw [hz]
    change outsideL2 Ω hΩ f x=_ at hx
    rw [hx]
    by_cases hxo : x∈Ω
    · simp [outsideCoefficient,hxo]
    · simp [outsideCoefficient,hxo,hy hxo]

theorem isClosed_L2_vanishing (Ω : Set X) (hΩ : MeasurableSet Ω) :
    IsClosed {f : Lp H 2 μ | ∀ᵐ x ∂μ, x∉Ω → f x=0} := by
  simpa only [← outsideL2_eq_zero_iff Ω hΩ] using
    (isClosed_eq (outsideL2 (H:=H) (μ:=μ) Ω hΩ).continuous continuous_const)

end General

variable {m : ℕ}

theorem periodicValue_vanishes_off
    (a b : CellCoordinates m) (hab : a≤b) (Ω P : Set (CellCoordinates m))
    (hΩ : MeasurableSet Ω) (k : Fin (m+1))
    (hface : ∀ y∈Icc (a∘k.succAbove) (b∘k.succAbove), k.insertNth (b k) y∉Ω)
    (u : PeriodicH10 a b Ω P) :
    ∀ᵐ x ∂volume.restrict (Icc a b), x∉Ω → periodicValue a b Ω P u x=0 := by
  have hc : IsClosed {v : PeriodicH10 a b Ω P |
      ∀ᵐ x ∂volume.restrict (Icc a b), x∉Ω → periodicValue a b Ω P v x=0} :=
    (isClosed_L2_vanishing Ω hΩ).preimage (periodicValue a b Ω P).continuous
  apply closure_minimal (s:=range (periodicTestEmbedding a b Ω P)) ?_ hc
    (denseRange_periodicTestEmbedding a b Ω P u)
  rintro v ⟨t,rfl⟩
  change ∀ᵐ x ∂volume.restrict (Icc a b), x∉Ω →
    periodicValue a b Ω P (periodicTestEmbedding a b Ω P t) x=0
  rw [periodicValue_test a b hab Ω P k hface]
  filter_upwards [(memLp_continuous_cell a b (periodicTest_contDiff t).continuous).coeFn_toLp] with x hx
  intro hxo
  exact hx.trans (t.property.2.1 x hxo)

theorem periodicH1Pair_value_vanishes_off
    (a b : CellCoordinates m) (hab : a≤b) (Ω P : Set (CellCoordinates m))
    (hΩ : MeasurableSet Ω) (k : Fin (m+1))
    (hface : ∀ y∈Icc (a∘k.succAbove) (b∘k.succAbove), k.insertNth (b k) y∉Ω)
    (u : PeriodicH10 a b Ω P) :
    ∀ᵐ x ∂volume, x∉Ω → (periodicH1Pair a b Ω P u).1 x=0 := by
  have h := (ae_restrict_iff' measurableSet_Icc).mp
    (periodicValue_vanishes_off a b hab Ω P hΩ k hface u)
  filter_upwards [h,periodicH1Pair_value_ae a b Ω P u] with x hx hy
  intro hxo
  rw [hy]
  by_cases hxc : x∈Icc a b
  · simpa only [cellZeroExtension,indicator_of_mem hxc] using hx hxc hxo
  · simp [cellZeroExtension,hxc]

theorem cutoff_periodicH1Pair_value_vanishes_off
    (a b : CellCoordinates m) (hab : a≤b) (Ω P : Set (CellCoordinates m))
    (hΩ : MeasurableSet Ω) (k : Fin (m+1))
    (hface : ∀ y∈Icc (a∘k.succAbove) (b∘k.succAbove), k.insertNth (b k) y∉Ω)
    (u : PeriodicH10 a b Ω P) (η : CellCoordinates m→ℝ) (hη : ContDiff ℝ 1 η)
    {M K : ℝ} (hM : ∀ x, |η x|≤M) (hK : ∀ x, ‖cellGradient η x‖≤K) :
    ∀ᵐ x ∂volume, x∉Ω →
      (OAI.Analysis.PDE.Weak.cutoffH1Pair η hη hM hK (periodicH1Pair a b Ω P u)).1 x=0 := by
  filter_upwards [periodicH1Pair_value_vanishes_off a b hab Ω P hΩ k hface u,
    OAI.Analysis.PDE.Weak.cutoffH1Pair_value_ae η hη hM hK (periodicH1Pair a b Ω P u)] with x hx hy
  intro hxo
  rw [hy,hx hxo,mul_zero]

end OAI.Analysis.PDE.Variational

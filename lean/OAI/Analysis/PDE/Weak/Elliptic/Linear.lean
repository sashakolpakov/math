import OAI.Analysis.PDE.Weak.Elliptic.Product

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
namespace OAI.Analysis.PDE.Weak

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (μ : Measure X) [IsLocallyFiniteMeasure μ]

omit [SecondCountableTopology X] [CompleteSpace E] in
theorem HasWeakDirectionalDerivativeOn.add_Lp
    {Ω : Set X} {v : X} {u g w z : Lp E 2 μ}
    (hu : HasWeakDirectionalDerivativeOn μ Ω v u g)
    (hw : HasWeakDirectionalDerivativeOn μ Ω v w z) :
    HasWeakDirectionalDerivativeOn μ Ω v (u + w : Lp E 2 μ) (g + z : Lp E 2 μ) := by
  have hraw : HasWeakDirectionalDerivativeOn μ Ω v
      (fun x ↦ u x + w x) (fun x ↦ g x + z x) := by
    intro φ hφ hs hsub
    have hD : Continuous (fun x ↦ fderiv ℝ φ x v) :=
      (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hDs := hs.fderiv_apply ℝ v
    have hi1 := integrable_inner_compact_test μ g hφ.continuous hs
    have hi2 := integrable_inner_compact_test μ z hφ.continuous hs
    have hi3 := integrable_inner_compact_test μ u hD hDs
    have hi4 := integrable_inner_compact_test μ w hD hDs
    simp_rw [inner_add_left]
    rw [integral_add hi1 hi2, integral_add hi3 hi4, hu φ hφ hs hsub, hw φ hφ hs hsub]
    ring
  apply OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.congr_on μ hraw
  · filter_upwards [Lp.coeFn_add u w] with x hx
    exact fun _ ↦ hx.symm
  · filter_upwards [Lp.coeFn_add g z] with x hx
    exact fun _ ↦ hx.symm

omit [CompleteSpace E] [IsLocallyFiniteMeasure μ] [BorelSpace X] [SecondCountableTopology X] in
theorem HasWeakDirectionalDerivativeOn.neg_Lp
    {Ω : Set X} {v : X} {u g : Lp E 2 μ}
    (hu : HasWeakDirectionalDerivativeOn μ Ω v u g) :
    HasWeakDirectionalDerivativeOn μ Ω v (-u : Lp E 2 μ) (-g : Lp E 2 μ) := by
  have hraw : HasWeakDirectionalDerivativeOn μ Ω v
      (fun x ↦ -u x) (fun x ↦ -g x) := by
    intro φ hφ hs hsub
    simp_rw [inner_neg_left, integral_neg]
    rw [hu φ hφ hs hsub]
  apply OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.congr_on μ hraw
  · filter_upwards [Lp.coeFn_neg u] with x hx
    exact fun _ ↦ hx.symm
  · filter_upwards [Lp.coeFn_neg g] with x hx
    exact fun _ ↦ hx.symm

omit [SecondCountableTopology X] [CompleteSpace E] in
theorem HasWeakDirectionalDerivativeOn.sub_Lp
    {Ω : Set X} {v : X} {u g w z : Lp E 2 μ}
    (hu : HasWeakDirectionalDerivativeOn μ Ω v u g)
    (hw : HasWeakDirectionalDerivativeOn μ Ω v w z) :
    HasWeakDirectionalDerivativeOn μ Ω v (u - w : Lp E 2 μ) (g - z : Lp E 2 μ) := by
  simpa only [sub_eq_add_neg] using hu.add_Lp μ (hw.neg_Lp μ)

omit [CompleteSpace E] [IsLocallyFiniteMeasure μ] [BorelSpace X] [SecondCountableTopology X] in
theorem HasWeakDirectionalDerivativeOn.zero_Lp (Ω : Set X) (v : X) :
    HasWeakDirectionalDerivativeOn μ Ω v (0 : Lp E 2 μ) (0 : Lp E 2 μ) := by
  have hz : HasWeakDirectionalDerivativeOn μ Ω v (fun _ : X ↦ (0 : E)) (fun _ ↦ 0) := by
    intro φ hφ hs hsub
    simp
  apply OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.congr_on μ hz
  · filter_upwards [Lp.coeFn_zero (E := E) (p := 2) (μ := μ)] with x hx
    exact fun _ ↦ hx.symm
  · filter_upwards [Lp.coeFn_zero (E := E) (p := 2) (μ := μ)] with x hx
    exact fun _ ↦ hx.symm

omit [SecondCountableTopology X] in
theorem HasWeakDirectionalDerivativeOn.map_Lp
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {Ω : Set X} {v : X} {u g : Lp E 2 μ}
    (hu : HasWeakDirectionalDerivativeOn μ Ω v u g) (L : E →L[ℝ] F) :
    HasWeakDirectionalDerivativeOn μ Ω v (L.compLp u) (L.compLp g) := by
  have hr := hu.operator_apply μ (fun _ ↦ L) contDiff_const u g
  have hc (x : X) : fderiv ℝ (fun _ : X ↦ L) x = 0 :=
    (hasFDerivAt_const (c := L) x).fderiv
  have hr' : HasWeakDirectionalDerivativeOn μ Ω v (fun x ↦ L (u x)) (fun x ↦ L (g x)) := by
    simpa only [hc, zero_apply, add_zero] using hr
  apply OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.congr_on μ hr'
  · filter_upwards [L.coeFn_compLp u] with x hx
    exact fun _ ↦ hx.symm
  · filter_upwards [L.coeFn_compLp g] with x hx
    exact fun _ ↦ hx.symm

end OAI.Analysis.PDE.Weak

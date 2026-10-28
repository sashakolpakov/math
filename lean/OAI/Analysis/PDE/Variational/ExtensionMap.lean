import OAI.Analysis.PDE.Variational.ZeroExtension

open Set Filter _root_.MeasureTheory
noncomputable section

namespace OAI.Analysis.PDE.Variational

variable {m : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [NormedSpace ℝ H] in
theorem cellZeroExtension_add (a b : CellCoordinates m)
    (f g : Lp H 2 (volume.restrict (Icc a b))) :
    cellZeroExtension a b (f+g) =ᵐ[volume] cellZeroExtension a b f + cellZeroExtension a b g := by
  have h := (ae_restrict_iff' measurableSet_Icc).mp (Lp.coeFn_add f g)
  filter_upwards [h] with x hx
  by_cases hxc : x∈Icc a b
  · simpa [cellZeroExtension, hxc] using hx hxc
  · simp [cellZeroExtension, hxc]

theorem cellZeroExtension_smul (a b : CellCoordinates m) (c : ℝ)
    (f : Lp H 2 (volume.restrict (Icc a b))) :
    cellZeroExtension a b (c • f) =ᵐ[volume] c • cellZeroExtension a b f := by
  have h := (ae_restrict_iff' measurableSet_Icc).mp (Lp.coeFn_smul c f)
  filter_upwards [h] with x hx
  by_cases hxc : x∈Icc a b
  · simpa [cellZeroExtension, hxc] using hx hxc
  · simp [cellZeroExtension, hxc]

def cellZeroExtensionLinear (a b : CellCoordinates m) :
    Lp H 2 (volume.restrict (Icc a b)) →ₗ[ℝ] Lp H 2 (volume : Measure (CellCoordinates m)) where
  toFun f := (memLp_cellZeroExtension a b f).toLp (cellZeroExtension a b f)
  map_add' f g := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (cellZeroExtension_add a b f g)
  map_smul' c f := by
    change _ = c • (memLp_cellZeroExtension a b f).toLp _
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (cellZeroExtension_smul a b c f)

theorem norm_cellZeroExtensionLinear (a b : CellCoordinates m)
    (f : Lp H 2 (volume.restrict (Icc a b))) : ‖cellZeroExtensionLinear a b f‖ = ‖f‖ := by
  change ‖(memLp_cellZeroExtension a b f).toLp (cellZeroExtension a b f)‖ = ‖f‖
  rw [Lp.norm_toLp, cellZeroExtension, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc,
    Lp.norm_def]

def cellZeroExtensionL2 (a b : CellCoordinates m) :
    Lp H 2 (volume.restrict (Icc a b)) →L[ℝ] Lp H 2 (volume : Measure (CellCoordinates m)) :=
  (cellZeroExtensionLinear a b).mkContinuous 1 (fun f ↦ by
    rw [norm_cellZeroExtensionLinear, one_mul])

theorem cellZeroExtensionL2_ae (a b : CellCoordinates m)
    (f : Lp H 2 (volume.restrict (Icc a b))) :
    cellZeroExtensionL2 a b f =ᵐ[volume] cellZeroExtension a b f :=
  (memLp_cellZeroExtension a b f).coeFn_toLp

end OAI.Analysis.PDE.Variational

import OAI.Analysis.PDE.Concentration.EuclideanLattice
import OAI.Analysis.PDE.Green.Localized.Flux

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.PDE.Green

theorem integral_linear_image {m : ℕ}
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) {S : Set (Fin m → ℝ)}
    (hS : MeasurableSet S) (f : (Fin m → ℝ) → ℝ) :
    (∫ x in L '' S, f x) = |L.toLinearEquiv.toLinearMap.det| * ∫ y in S, f (L y) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume
    (f := fun x => L x) (f' := fun _ => L.toContinuousLinearMap) (s := S) hS
    (fun x hx => L.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt)
    L.injective.injOn f
  rw [h]
  simp only [smul_eq_mul, integral_const_mul]
  rfl

/-- Quantitative Piola transport. The normal error is unchanged by the
linear chart; the only scale factor is its actual volume Jacobian. -/
theorem weighted_parallelepiped_divergence_bound {m : ℕ}
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (hF : ContDiff ℝ 1 F)
    {r v : (Fin (m + 1) → ℝ) → ℝ} (hr : ContDiff ℝ 1 r) (hv : Continuous v)
    {ε W C : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ k : ℕ, (∫ x in Icc a b, OAI.Analysis.PDE.Green.normalCutoffWeight (r (L x)) k * ‖v (L x)‖) ≤ W)
    (hbound : ∀ x ∈ L '' Icc a b, ‖fderiv ℝ r x (F x)‖ ≤ ε * ‖v x‖ + C * ‖r x‖)
    (hface : OAI.Analysis.PDE.Green.CompatibleBoxFaces a b (r ∘ L) (fun i x => linearPiola L F x i)) :
    ‖∫ x in L '' Icc a b ∩ {x | r x < 0}, coordinateDivergence F x‖ ≤
      |L.toLinearEquiv.toLinearMap.det| * (ε * W) := by
  let G := linearPiola L F
  have hG := contDiff_linearPiola L hF
  have hG' (i) : ContDiff ℝ 1 (fun x => G x i) :=
    (ContinuousLinearMap.proj i : (Fin (m + 1) → ℝ) →L[ℝ] ℝ).contDiff.comp hG
  have hbound' (x : Fin (m + 1) → ℝ) (hx : x ∈ Icc a b) :
      ‖∑ i, fderiv ℝ (r ∘ L) x (Pi.single i 1) * G x i‖ ≤
        ε * ‖v (L x)‖ + C * ‖r (L x)‖ := by
    rw [sum_fderiv_coordinate_mul]
    rw [fderiv_linearPiola_normal L F (hr.differentiable (by norm_num) _)]
    exact hbound _ (mem_image_of_mem L hx)
  have hz := OAI.Analysis.PDE.Green.weighted_small_divergence_of_normal_bound a b hab
    (fun i x => G x i) hG' (hr.comp L.contDiff) (hv.comp L.continuous) hε hW hbound' hface
  have hd (x : Fin (m + 1) → ℝ) :
      (∑ i, fderiv ℝ (fun y => G y i) x (Pi.single i 1)) = coordinateDivergence F (L x) := by
    rw [← coordinateDivergence_eq_components (hG.differentiable (by norm_num) x)]
    exact coordinateDivergence_linearPiola L (hF.differentiable (by norm_num) _)
  simp_rw [hd] at hz
  have hset : L '' (Icc a b ∩ {x | r (L x) < 0}) = L '' Icc a b ∩ {x | r x < 0} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hrx⟩, rfl⟩
      exact ⟨mem_image_of_mem L hx, hrx⟩
    · rintro ⟨⟨x, hx, rfl⟩, hrx⟩
      exact ⟨x, ⟨hx, hrx⟩, rfl⟩
  have hS : MeasurableSet (Icc a b ∩ {x | r (L x) < 0}) :=
    measurableSet_Icc.inter ((isOpen_lt (hr.continuous.comp L.continuous) continuous_const).measurableSet)
  have hJ := integral_linear_image L hS (coordinateDivergence F)
  rw [← hset, hJ]
  rw [norm_mul, Real.norm_eq_abs, abs_abs]
  exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)

theorem weighted_euclidean_lattice_divergence_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : ι → EuclideanSpace ℝ ι → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r v : EuclideanSpace ℝ ι → ℝ} (hr : ContDiff ℝ 1 r) (hv : Continuous v)
    {ε W C : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ k : ℕ, (∫ x in Icc a b,
      OAI.Analysis.PDE.Green.normalCutoffWeight (r ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L x))) k *
        ‖v ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L x))‖) ≤ W)
    (hbound : ∀ x ∈ euclideanLatticeCell c L a b,
      ‖∑ i, fderiv ℝ r x (EuclideanSpace.single i 1) * F i x‖ ≤ ε * ‖v x‖ + C * ‖r x‖)
    (hface : CompatibleLatticeFaces c L a b r F) :
    ‖∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0},
      ∑ i, fderiv ℝ (F i) x (EuclideanSpace.single i 1)‖ ≤
        |L.toLinearEquiv.toLinearMap.det| * (ε * W) := by
  let e := OAI.Analysis.PDE.Green.euclideanCoordinates c
  let G := latticeCoordinateField c F
  have hG : ContDiff ℝ 1 G := contDiff_pi.mpr (fun i => (hF (c.symm i)).comp e.symm.contDiff)
  have hdr (y w : Fin (m + 1) → ℝ) :
      fderiv ℝ (r ∘ e.symm) y w = fderiv ℝ r (e.symm y) (e.symm w) :=
    OAI.Analysis.PDE.Green.fderiv_comp_linear_apply e.symm.toContinuousLinearMap hr y w
  have hs (i) : e.symm (Pi.single i 1) = EuclideanSpace.single (c.symm i) 1 :=
    OAI.Analysis.PDE.Green.euclideanCoordinates_symm_single c i
  have hb (y : Fin (m + 1) → ℝ) (hy : y ∈ L '' Icc a b) :
      ‖fderiv ℝ (r ∘ e.symm) y (G y)‖ ≤ ε * ‖v (e.symm y)‖ + C * ‖r (e.symm y)‖ := by
    rw [← sum_fderiv_coordinate_mul]
    simp_rw [hdr, hs]
    change ‖∑ i, fderiv ℝ r (e.symm y) (EuclideanSpace.single (c.symm i) 1) *
      F (c.symm i) (e.symm y)‖ ≤ _
    rw [c.symm.sum_comp (fun i => fderiv ℝ r (e.symm y) (EuclideanSpace.single i 1) * F i (e.symm y))]
    exact hbound _ (by simpa [euclideanLatticeCell, e] using hy)
  have hz := weighted_parallelepiped_divergence_bound L a b hab G hG
    (hr.comp e.symm.contDiff) (hv.comp e.symm.continuous) hε hW hb hface
  have hd (y : Fin (m + 1) → ℝ) : coordinateDivergence G y =
      ∑ i, fderiv ℝ (F i) (e.symm y) (EuclideanSpace.single i 1) := by
    rw [coordinateDivergence_eq_components (hG.differentiable (by norm_num) y)]
    have hi (i : Fin (m + 1)) : fderiv ℝ (fun z => G z i) y (Pi.single i 1) =
        fderiv ℝ (F (c.symm i)) (e.symm y) (EuclideanSpace.single (c.symm i) 1) := by
      have heq : fderiv ℝ (fun z => F (c.symm i) (e.symm z)) y (Pi.single i 1) =
          fderiv ℝ (F (c.symm i)) (e.symm y) (e.symm (Pi.single i 1)) :=
        OAI.Analysis.PDE.Green.fderiv_comp_linear_apply e.symm.toContinuousLinearMap (hF (c.symm i)) y _
      exact heq.trans (congrArg (fderiv ℝ (F (c.symm i)) (e.symm y)) (hs i))
    simp_rw [hi]
    exact c.symm.sum_comp (fun i => fderiv ℝ (F i) (e.symm y) (EuclideanSpace.single i 1))
  simp_rw [hd] at hz
  have hme : MeasurePreserving e := OAI.Analysis.PDE.Green.measurePreserving_euclideanCoordinates c
  have hm := hme.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding
    (fun y => ∑ i, fderiv ℝ (F i) (e.symm y) (EuclideanSpace.single i 1))
    (L '' Icc a b ∩ {y | r (e.symm y) < 0})
  have hEq : (∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0},
      ∑ i, fderiv ℝ (F i) x (EuclideanSpace.single i 1)) =
      ∫ y in L '' Icc a b ∩ {y | r (e.symm y) < 0},
        ∑ i, fderiv ℝ (F i) (e.symm y) (EuclideanSpace.single i 1) := by
    simpa only [euclideanLatticeCell, Set.preimage_inter, Set.preimage_ofPred_eq, e.symm_apply_apply] using hm
  rw [hEq]
  exact hz

end OAI.Analysis.PDE.Concentration

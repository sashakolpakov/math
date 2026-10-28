import OAI.RepresentationTheory.Weil.AdelicSplitting.LinearSubstitution

/-! # Determinant Measure -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.DeterminantMeasure.LocalAnalysis

noncomputable section

/- AdelicSplitting-owned copy of the checked LocalWeil analytic helper development.
Kept in a separate namespace so this proof commit has no dependency on
another task's uncommitted modules. -/

/-! The determinant Jacobian over an arbitrary characteristic-zero local field. -/

open _root_.MeasureTheory _root_.Matrix Set
open scoped NNReal ENNReal Pointwise BigOperators Classical

section Modulus

variable (k : Type) [NormedField k] [LocallyCompactSpace k]

/-- Haar modulus extended by zero. It is multiplicative; no triangle
inequality is asserted (at a complex place it is the squared modulus). -/
def haarModulus : k →*₀ ℝ≥0 where
  toFun a := if ha : a = 0 then 0 else distribHaarChar k (Units.mk0 a ha)
  map_zero' := by simp
  map_one' := by
    rw [dite_eq_right one_ne_zero]
    rw [show Units.mk0 (1 : k) one_ne_zero = 1 from Units.ext rfl]
    exact map_one (distribHaarChar k)
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    simp only [ha, hb, mul_ne_zero ha hb, ↓reduceDIte]
    rw [show Units.mk0 (a * b) (mul_ne_zero ha hb) = Units.mk0 a ha * Units.mk0 b hb
      from Units.ext rfl]
    exact map_mul _ _ _

theorem haarModulus_unit (a : kˣ) : haarModulus k (a : k) = distribHaarChar k a := by
  change (if ha : (a : k) = 0 then 0 else distribHaarChar k (Units.mk0 (a : k) ha)) = _
  rw [dite_eq_right a.ne_zero]
  congr 1
  exact Units.ext rfl

theorem haarModulus_pos {a : k} (ha : a ≠ 0) : 0 < haarModulus k a := by
  change 0 < if h : a = 0 then 0 else distribHaarChar k (Units.mk0 a h)
  rw [dite_eq_right ha]
  exact distribHaarChar_pos

end Modulus

section Haar

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
  (μ : Measure k) [μ.IsAddHaarMeasure]

theorem haarModulus_mul_preimage {a : k} (ha : a ≠ 0) (s : Set k) :
    (haarModulus k a : ℝ≥0∞) * μ ((a * ·) ⁻¹' s) = μ s := by
  let u : kˣ := Units.mk0 a ha
  have h := distribHaarChar_mul μ u ((fun x => a * x) ⁻¹' s)
  have hu : (haarModulus k a : ℝ≥0) = distribHaarChar k u :=
    haarModulus_unit k u
  rw [hu]
  convert h using 1
  congr 1
  change s = u • ((fun x => (u : k) * x) ⁻¹' s)
  rw [show (fun x => (u : k) * x) = (fun x => u • x) from rfl, preimage_smul]
  simp

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem haar_smul_map_diagonal {D : ι → k} (hD : det (diagonal D) ≠ 0) :
    (haarModulus k (det (diagonal D)) : ℝ≥0∞) •
      Measure.map (Matrix.toLin' (diagonal D)) (Measure.pi (fun _ : ι => μ)) =
        Measure.pi (fun _ : ι => μ) := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.smul_apply, Measure.map_apply]
  · have hpre : (Matrix.toLin' (diagonal D) ⁻¹' Set.pi Set.univ s) =
        Set.pi Set.univ (fun i => (D i * ·) ⁻¹' s i) := by
      ext f
      simp only [mem_univ_pi, mem_preimage, diagonal_toLin',
        LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.coe_proj, smul_eq_mul]
    rw [hpre, Measure.pi_pi, det_diagonal, map_prod, ENNReal.ofNNReal_finsetProd,
      smul_eq_mul, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact haarModulus_mul_preimage μ
      ((Finset.prod_ne_zero_iff.mp (by simpa only [det_diagonal] using hD)) i (Finset.mem_univ i)) _
  · exact (LinearMap.continuous_on_pi _).measurable
  · exact MeasurableSet.univ_pi hs

theorem haar_preserving_transvection (t : TransvectionStruct ι k) :
    MeasurePreserving (Matrix.toLin' t.toMatrix)
      (Measure.pi (fun _ : ι => μ)) (Measure.pi (fun _ : ι => μ)) := by
  have ht : Measurable (Matrix.toLin' t.toMatrix) :=
    (LinearMap.continuous_on_pi _).measurable
  refine ⟨ht, (Measure.pi_eq fun s hs => ?_).symm⟩
  have h2s : MeasurableSet (univ.pi s) := .pi countable_univ fun i _ => hs i
  simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]
  refine lintegral_eq_of_lmarginal_eq {t.i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  cases t with
  | mk i j hij c =>
    simp [transvection, single_mulVec, hij.symm, ← Function.update_add,
      lintegral_add_right_eq_self (μ := μ)
        (fun xᵢ => indicator (univ.pi s) 1 (Function.update x i xᵢ))]

theorem map_matrix_haar_eq_smul {M : Matrix ι ι k} (hM : det M ≠ 0) :
    Measure.map (Matrix.toLin' M) (Measure.pi (fun _ : ι => μ)) =
      (haarModulus k ((det M)⁻¹) : ℝ≥0∞) • Measure.pi (fun _ : ι => μ) := by
  apply diagonal_transvection_induction_of_det_ne_zero _ M hM
  · intro D hD
    conv_rhs => rw [← haar_smul_map_diagonal μ hD]
    rw [smul_smul, ← ENNReal.coe_mul, ← map_mul, inv_mul_cancel₀ hD, map_one,
      ENNReal.coe_one, one_smul]
  · intro t
    simp only [TransvectionStruct.det, inv_one, map_one, ENNReal.coe_one,
      one_smul, (haar_preserving_transvection μ t).map_eq]
  · intro A B _ _ IHA IHB
    rw [Matrix.toLin'_mul, det_mul, LinearMap.coe_comp, ← Measure.map_map
      (LinearMap.continuous_on_pi (Matrix.toLin' A)).measurable
      (LinearMap.continuous_on_pi (Matrix.toLin' B)).measurable,
      IHB, Measure.map_smul _ (LinearMap.continuous_on_pi (Matrix.toLin' A)).measurable.aemeasurable, IHA, smul_smul, ← ENNReal.coe_mul, ← map_mul, _root_.mul_inv_rev]

end Haar

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}

theorem coordinateJacobian_eq_determinant (A : Local.FunctionsMetaplectic.Construction.GeneralLinear k n) :
    LinearSubstitution.LocalAnalysis.coordinateJacobian (LinearSubstitution.LocalAnalysis.positionAddEquiv A) = Local.FunctionsMetaplectic.Construction.localModulus k (Local.FunctionsMetaplectic.Construction.determinantUnit k A) := by
  let ν : Measure (Local.FunctionsMetaplectic.Construction.Position k n) := Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k))
  let c : ℝ≥0 := haarModulus k (det (A : Matrix (Fin n) (Fin n) k))
  have hdet : det (A : Matrix (Fin n) (Fin n) k) ≠ 0 := (Local.FunctionsMetaplectic.Construction.determinantUnit k A).ne_zero
  have hc : c ≠ 0 := (haarModulus_pos k hdet).ne'
  have hmap : ν.map (LinearSubstitution.LocalAnalysis.positionAddEquiv A) = c⁻¹ • ν := by
    have hm := map_matrix_haar_eq_smul (Measure.addHaar : Measure k) hdet
    rw [map_inv₀] at hm
    exact hm
  let : (c⁻¹ • ν).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul ν (inv_ne_zero hc)
  have hforward : Measure.addHaarScalarFactor (ν.map (LinearSubstitution.LocalAnalysis.positionAddEquiv A)) ν = c⁻¹ := by
    simp only [hmap, Measure.addHaarScalarFactor_smul, Measure.addHaarScalarFactor_self,
      smul_eq_mul, mul_one]
  have hprod := Measure.addHaarScalarFactor_eq_mul ν (ν.map (LinearSubstitution.LocalAnalysis.positionAddEquiv A)) ν
  rw [Measure.addHaarScalarFactor_self, hforward] at hprod
  have heq : addEquivAddHaarChar (LinearSubstitution.LocalAnalysis.positionAddEquiv A) = c := by
    rw [addEquivAddHaarChar_eq ν]
    apply mul_right_cancel₀ (inv_ne_zero hc)
    rw [← hprod, mul_inv_cancel₀ hc]
  unfold LinearSubstitution.LocalAnalysis.coordinateJacobian Local.FunctionsMetaplectic.Construction.localModulus
  rw [heq]
  exact congrArg (fun x : ℝ≥0 => (x : ℝ)) (haarModulus_unit k (Local.FunctionsMetaplectic.Construction.determinantUnit k A))

theorem normalizedCoordinate_matrix_apply
    (A : Local.FunctionsMetaplectic.Construction.GeneralLinear k n) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : Local.FunctionsMetaplectic.Construction.Position k n) :
    (LinearSubstitution.LocalAnalysis.normalizedCoordinate (LinearSubstitution.LocalAnalysis.positionAddEquiv A) f).val x =
      ((Real.sqrt (Local.FunctionsMetaplectic.Construction.localModulus k (Local.FunctionsMetaplectic.Construction.determinantUnit k A)))⁻¹ : ℂ) *
        f.val (Matrix.mulVec (↑(A⁻¹) : Matrix (Fin n) (Fin n) k) x) := by
  rw [LinearSubstitution.LocalAnalysis.normalizedCoordinate_apply, LinearSubstitution.LocalAnalysis.coordinateScale, coordinateJacobian_eq_determinant]
  rw [Complex.ofReal_inv]
  rfl

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.DeterminantMeasure.LocalAnalysis

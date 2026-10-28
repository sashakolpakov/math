import OAI.Analysis.Fourier.BochnerRiesz.MaximalLp

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

abbrev LargeRadius := Ici (1 : ℝ)

def largeRadiusPositive (R : LargeRadius) : PositiveRadius :=
  ⟨R, by change 0 < (R : ℝ); exact lt_of_lt_of_le zero_lt_one R.property⟩

def largeRadiusInclusion : C(LargeRadius, PositiveRadius) where
  toFun := largeRadiusPositive
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact continuous_subtype_val

def largeRadiusInverse : C(LargeRadius, InverseRadius) where
  toFun R := inverseRadiusAt R
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    change Continuous (fun R : LargeRadius => min 1 (max 0 (R : ℝ)⁻¹))
    exact continuous_const.min (continuous_const.max
      (continuous_subtype_val.inv₀ (fun R => ne_of_gt (lt_of_lt_of_le zero_lt_one R.property))))

def brBoundedToLarge : BoundedContinuousFunction PositiveRadius ℂ →L[ℂ]
    BoundedContinuousFunction LargeRadius ℂ :=
  BoundedContinuousFunction.compContinuousCLM ℂ ℂ largeRadiusInclusion

def brCompactToLarge : C(InverseRadius, ℂ) →L[ℂ] BoundedContinuousFunction LargeRadius ℂ :=
  LinearMap.mkContinuous
    { toFun := fun u => BoundedContinuousFunction.ofNormedAddCommGroup
        (fun R => u (largeRadiusInverse R)) (u.continuous.comp largeRadiusInverse.continuous)
        ‖u‖ (fun R => u.norm_coe_le_norm _)
      map_add' := by intro u v; ext R; rfl
      map_smul' := by intro c u; ext R; rfl }
    1 (fun u => by
      rw [one_mul]
      apply (BoundedContinuousFunction.norm_le (norm_nonneg u)).mpr
      intro R
      exact u.norm_coe_le_norm _)

@[simp] theorem brBoundedToLarge_apply (u : BoundedContinuousFunction PositiveRadius ℂ)
    (R : LargeRadius) : brBoundedToLarge u R = u (largeRadiusPositive R) := rfl

@[simp] theorem brCompactToLarge_apply (u : C(InverseRadius, ℂ)) (R : LargeRadius) :
    brCompactToLarge u R = u (inverseRadiusAt R) := rfl

theorem brLarge_agreement_schwartz {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    brBoundedToLarge (brBoundedFamily hδ f x) = brCompactToLarge (brCompactFamily hδ f x) := by
  ext R
  change OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x = brCompactFamily hδ f x (inverseRadiusAt R)
  have hr : 0 < (R : ℝ) := lt_of_lt_of_le zero_lt_one R.property
  have ht : 0 < (inverseRadiusAt R : ℝ) := by rw [inverseRadiusAt_eq R.property]; positivity
  rw [brCompactFamily_pos hδ f x _ ht, inverseRadiusAt_eq R.property, inv_inv]

theorem brBounded_compact_agreement {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hpt : p ≠ ⊤) {δ : ℝ} (hδ : 0 ≤ δ)
    (W : BrLp n p →L[ℂ] BrBoundedLp n p) (U : BrLp n p →L[ℂ] BrFamilyLp n p)
    (hW : ∀ f : SchwartzMap (Space n) ℂ,
      (W (f.toLp p volume) : Space n → BoundedContinuousFunction PositiveRadius ℂ) =ᵐ[volume]
        brBoundedFamily hδ f)
    (hU : ∀ f : SchwartzMap (Space n) ℂ,
      (U (f.toLp p volume) : Space n → C(InverseRadius, ℂ)) =ᵐ[volume] brCompactFamily hδ f)
    (f : BrLp n p) :
    ∀ᵐ x ∂volume, ∀ R : ℝ, 1 ≤ R → brFullRepresentative (W f) R x = brFamilyRepresentative (U f) R x := by
  let L := brBoundedToLarge.compLpL p (volume : Measure (Space n))
  let K := brCompactToLarge.compLpL p (volume : Measure (Space n))
  have hd : DenseRange (fun g : SchwartzMap (Space n) ℂ => g.toLp p volume) :=
    SchwartzMap.denseRange_toLpCLM hpt
  have hbase (g : SchwartzMap (Space n) ℂ) : L (W (g.toLp p volume)) = K (U (g.toLp p volume)) := by
    apply Lp.ext
    filter_upwards [brBoundedToLarge.coeFn_compLpL (W (g.toLp p volume)),
      brCompactToLarge.coeFn_compLpL (U (g.toLp p volume)), hW g, hU g] with x hL hK hw hu
    exact hL.trans ((congrArg brBoundedToLarge hw).trans
      ((brLarge_agreement_schwartz hδ g x).trans ((congrArg brCompactToLarge hu).symm.trans hK.symm)))
  have he : (fun f => L (W f)) = (fun f => K (U f)) :=
    hd.equalizer (L.continuous.comp W.continuous) (K.continuous.comp U.continuous) (funext hbase)
  have hLf := brBoundedToLarge.coeFn_compLpL (W f)
  have hKf := brCompactToLarge.coeFn_compLpL (U f)
  have he' : L (W f) = K (U f) := congrFun he f
  change (L (W f) : Space n → BoundedContinuousFunction LargeRadius ℂ) =ᵐ[volume] _ at hLf
  rw [he'] at hLf
  filter_upwards [hLf, hKf] with x hx hy
  have hz := hx.symm.trans hy
  intro R hR
  have h := DFunLike.congr_fun hz (⟨R, hR⟩ : LargeRadius)
  have hr : 0 < R := lt_of_lt_of_le zero_lt_one hR
  simpa only [brFullRepresentative, dite_eq_left hr, brFamilyRepresentative,
    brBoundedToLarge_apply, brCompactToLarge_apply, largeRadiusPositive] using h

end OAI.Analysis.Fourier.BochnerRiesz

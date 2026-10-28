import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.KillingDeterminant
import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingBracketLocalRigidity

/-! # Orbit Minimum -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.OrbitMinimum.Construction

noncomputable section

section

/-! Volume-preserving changes of basis form a closed orbit on a
real Lie bracket with nondegenerate Killing form. -/

open scoped Classical _root_.Topology
open Filter Set

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

local instance orbitEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance orbitEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance orbitBilinear_normed : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance orbitBilinear_space : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance orbitBilinear_finite : FiniteDimensional ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance orbitTrilinear_normed : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance orbitTrilinear_space : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance orbitJacobiOperator_normed : NormedAddCommGroup
    ((L →L[ℝ] L →L[ℝ] L) →L[ℝ] (L →L[ℝ] L →L[ℝ] L →L[ℝ] L)) := inferInstance
local instance orbitJacobiOperator_space : NormedSpace ℝ
    ((L →L[ℝ] L →L[ℝ] L) →L[ℝ] (L →L[ℝ] L →L[ℝ] L →L[ℝ] L)) := inferInstance

omit [FiniteDimensional ℝ L] in
theorem continuousBracketChange_trans (e f : L ≃L[ℝ] L) (B : L →L[ℝ] L →L[ℝ] L) :
    ContinuousBracketChange.Construction.continuousBracketChange f (ContinuousBracketChange.Construction.continuousBracketChange e B) =
      ContinuousBracketChange.Construction.continuousBracketChange (e.trans f) B := by
  ext x y
  rfl

omit [FiniteDimensional ℝ L] in
theorem continuousBracketChange_refl (B : L →L[ℝ] L →L[ℝ] L) :
    ContinuousBracketChange.Construction.continuousBracketChange (ContinuousLinearEquiv.refl ℝ L) B = B := by
  ext x y
  rfl

omit [FiniteDimensional ℝ L] in
theorem abs_det_one_trans (e f : L ≃L[ℝ] L)
    (he : |LinearMap.det e.toLinearMap| = 1) (hf : |LinearMap.det f.toLinearMap| = 1) :
    |LinearMap.det (e.trans f).toLinearMap| = 1 := by
  change |LinearMap.det (f.toLinearMap.comp e.toLinearMap)| = 1
  rw [LinearMap.det_comp, abs_mul, he, hf, one_mul]

omit [FiniteDimensional ℝ L] in
theorem abs_det_one_symm (e : L ≃L[ℝ] L) (he : |LinearMap.det e.toLinearMap| = 1) :
    |LinearMap.det e.symm.toLinearMap| = 1 := by
  have h := congrArg (fun x : ℝ => |x|) e.toLinearEquiv.det_mul_det_symm
  change |LinearMap.det e.symm.toLinearEquiv.toLinearMap| = 1
  rw [ContinuousLinearEquiv.toLinearEquiv_symm]
  simpa only [abs_mul, abs_one, he, one_mul] using h

def bracketVolumeOrbit (B : L →L[ℝ] L →L[ℝ] L) : Set (L →L[ℝ] L →L[ℝ] L) :=
  {C | ∃ e : L ≃L[ℝ] L, |LinearMap.det e.toLinearMap| = 1 ∧ C = ContinuousBracketChange.Construction.continuousBracketChange e B}

omit [FiniteDimensional ℝ L] in
theorem bracketVolumeOrbit_self (B : L →L[ℝ] L →L[ℝ] L) : B ∈ bracketVolumeOrbit B := by
  refine ⟨ContinuousLinearEquiv.refl ℝ L, ?_, (continuousBracketChange_refl B).symm⟩
  change |LinearMap.det (LinearMap.id : L →ₗ[ℝ] L)| = 1
  simp

theorem isClosed_continuousLieBrackets :
    IsClosed {B : L →L[ℝ] L →L[ℝ] L | ContinuousBracketConstraints.Construction.IsContinuousLieBracket B} := by
  have ha : IsClosed {B : L →L[ℝ] L →L[ℝ] L | ∀ x, B x x = 0} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    exact isClosed_eq ((continuous_id.clm_apply continuous_const).clm_apply continuous_const)
      continuous_const
  have hj : Continuous (fun B : L →L[ℝ] L →L[ℝ] L => ContinuousJacobi.Construction.continuousJacobiPair B B) :=
    (ContinuousJacobi.Construction.continuousJacobiPair.continuous.comp continuous_id).clm_apply continuous_id
  exact ha.inter (isClosed_eq hj continuous_const)

theorem bracketVolumeOrbit_isClosed
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) : IsClosed (bracketVolumeOrbit B) := by
  let b := Module.finBasis ℝ L
  let X : Set (L →L[ℝ] L →L[ℝ] L) :=
    {C | ContinuousBracketConstraints.Construction.IsContinuousLieBracket C ∧ KillingDeterminant.Construction.bracketKillingDeterminant b C = KillingDeterminant.Construction.bracketKillingDeterminant b B}
  have hX : IsClosed X := isClosed_continuousLieBrackets.inter
    (isClosed_eq (KillingDeterminant.Construction.bracketKillingDeterminant_continuous b) continuous_const)
  have hsub : bracketVolumeOrbit B ⊆ X := by
    rintro C ⟨e, he, rfl⟩
    exact ⟨ContinuousBracketConstraints.Construction.isContinuousLieBracket_change e B hB,
      KillingDeterminant.Construction.bracketKillingDeterminant_change_of_abs_det_one b e he B⟩
  apply isClosed_of_closure_subset
  intro C hC
  have hCX := closure_minimal hsub hX hC
  have hKC : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm C).Nondegenerate := by
    apply (KillingDeterminant.Construction.bracketKillingDeterminant_ne_zero b C).mp
    rw [hCX.2]
    exact (KillingDeterminant.Construction.bracketKillingDeterminant_ne_zero b B).mpr hK
  have hnear := KillingBracketLocalRigidity.Construction.killing_bracket_local_rigidity C hCX.1 hKC
  obtain ⟨D, hDO, hDC⟩ := ((mem_closure_iff_frequently.mp hC).and_eventually hnear).exists
  have hDX := hsub hDO
  obtain ⟨e, he⟩ := hDC hDX.1
  have hdet : |LinearMap.det e.toLinearMap| = 1 := by
    apply KillingDeterminant.Construction.abs_det_one_of_bracketKillingDeterminant_eq b e C hKC
    rw [← he, hDX.2, hCX.2]
  obtain ⟨f, hf, hDf⟩ := hDO
  refine ⟨f.trans e.symm, abs_det_one_trans f e.symm hf (abs_det_one_symm e hdet), ?_⟩
  rw [← continuousBracketChange_trans, ← hDf, he, ContinuousBracketChange.Construction.continuousBracketChange_inverse]

end

/-! Closed volume-preserving bracket orbits attain a minimum norm,
also after arbitrary continuous linear coordinates are chosen. -/

open scoped Classical
open Set

theorem exists_min_norm_on_closed_set
    {V : Type*} [NormedAddCommGroup V] [ProperSpace V]
    (s : Set V) (hs : IsClosed s) (hne : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, ‖x‖ ≤ ‖y‖ := by
  obtain ⟨x₀, hx₀⟩ := hne
  let K := Metric.closedBall (0 : V) ‖x₀‖ ∩ s
  have hK : IsCompact K := (isCompact_closedBall 0 ‖x₀‖).inter_right hs
  have hKn : K.Nonempty := ⟨x₀, by simpa only [K, mem_inter_iff, Metric.mem_closedBall, dist_zero_right] using
    (show ‖x₀‖ ≤ ‖x₀‖ ∧ x₀ ∈ s from ⟨le_rfl, hx₀⟩)⟩
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hKn continuous_norm.continuousOn
  refine ⟨x, hx.2, fun y hy => ?_⟩
  by_cases hyl : ‖y‖ ≤ ‖x₀‖
  · exact hmin ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hyl, hy⟩
  · have hxl : ‖x‖ ≤ ‖x₀‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx.1
    exact hxl.trans (le_of_not_ge hyl)

theorem killing_bracket_orbit_has_minimum
    {L V : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Φ : (L →L[ℝ] L →L[ℝ] L) ≃L[ℝ] V)
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    ∃ e : L ≃L[ℝ] L, |LinearMap.det e.toLinearMap| = 1 ∧
      ∀ f : L ≃L[ℝ] L, |LinearMap.det f.toLinearMap| = 1 →
        ‖Φ (ContinuousBracketChange.Construction.continuousBracketChange e B)‖ ≤ ‖Φ (ContinuousBracketChange.Construction.continuousBracketChange f B)‖ := by
  let : ProperSpace V := FiniteDimensional.proper ℝ V
  have hc : IsClosed (Φ '' bracketVolumeOrbit B) :=
    Φ.toHomeomorph.isClosedMap _ (bracketVolumeOrbit_isClosed B hB hK)
  have hn : (Φ '' bracketVolumeOrbit B).Nonempty :=
    ⟨Φ B, B, bracketVolumeOrbit_self B, rfl⟩
  obtain ⟨x, hx, hmin⟩ := exists_min_norm_on_closed_set (Φ '' bracketVolumeOrbit B) hc hn
  obtain ⟨C, ⟨e, he, hCe⟩, hCx⟩ := hx
  refine ⟨e, he, fun f hf => ?_⟩
  rw [← hCe, hCx]
  exact hmin _ ⟨ContinuousBracketChange.Construction.continuousBracketChange f B, ⟨f, hf, rfl⟩, rfl⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.OrbitMinimum.Construction

import OAI.Geometry.ComplexBall.QuotientAtlas

/-! # Covering Atlas -/

namespace OAI.Geometry.ComplexBall.CoveringAtlas.ArithmeticQuotient

noncomputable section

/-! A complex atlas on any space presented by a free ball quotient covering.
This permits the actual cone quotient to carry the same local geometry. -/

open scoped Classical _root_.Manifold ContDiff
open _root_.Topology

variable (b : ℂ) (hb : b.re < 0) (Γ : Subgroup (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b))
    {Q : Type*} [TopologicalSpace Q] (f : ArithmeticQuotientBoostBall.Ball b → Q) (hf : IsQuotientCoveringMap f Γ)

def coveringBallBranch (z : ArithmeticQuotientBoostBall.Ball b) : OpenPartialHomeomorph Q (ArithmeticQuotientBoostBall.Ball b) :=
  hf.isCoveringMap.isLocalHomeomorph.localInverseAt z

def coveringBallChart (z : ArithmeticQuotientBoostBall.Ball b) : OpenPartialHomeomorph Q ArithmeticQuotientBoostBall.BallCoordinates :=
  (coveringBallBranch b Γ f hf z).trans (QuotientAtlas.Arithmetic.ballInclusion b hb)

lemma coveringBallChart_source (z : ArithmeticQuotientBoostBall.Ball b) :
    (coveringBallChart b hb Γ f hf z).source = (coveringBallBranch b Γ f hf z).source := by
  simp [coveringBallChart, QuotientAtlas.Arithmetic.ballInclusion_source]

lemma coveringBallChart_apply (z : ArithmeticQuotientBoostBall.Ball b) (q : Q) :
    coveringBallChart b hb Γ f hf z q = (coveringBallBranch b Γ f hf z q).val := rfl

lemma coveringBallChart_symm_apply (z : ArithmeticQuotientBoostBall.Ball b) (w : ArithmeticQuotientBoostBall.BallCoordinates) :
    (coveringBallChart b hb Γ f hf z).symm w = f ((QuotientAtlas.Arithmetic.ballInclusion b hb).symm w) :=
  congrFun (hf.isCoveringMap.isLocalHomeomorph.localInverseAt_symm z) _

lemma coveringBallChart_target_subset (z : ArithmeticQuotientBoostBall.Ball b) :
    (coveringBallChart b hb Γ f hf z).target ⊆ (ArithmeticQuotientBoostBall.ballOpen b : Set ArithmeticQuotientBoostBall.BallCoordinates) := by
  intro w hw
  exact (QuotientAtlas.Arithmetic.ballInclusion_target b hb) ▸ hw.1

lemma coveringBallChart_target_self (z : ArithmeticQuotientBoostBall.Ball b) :
    z.val ∈ (coveringBallChart b hb Γ f hf z).target := by
  change z.val ∈ (QuotientAtlas.Arithmetic.ballInclusion b hb).target ∧
    (QuotientAtlas.Arithmetic.ballInclusion b hb).symm z.val ∈ (coveringBallBranch b Γ f hf z).target
  constructor
  · rw [QuotientAtlas.Arithmetic.ballInclusion_target]
    exact z.property
  · rw [QuotientAtlas.Arithmetic.ballInclusion_symm_coe]
    exact hf.isCoveringMap.isLocalHomeomorph.self_mem_localInverseAt_target

@[instance_reducible] def coveringBallAtlas : ChartedSpace ArithmeticQuotientBoostBall.BallCoordinates Q where
  atlas := Set.range (coveringBallChart b hb Γ f hf)
  chartAt q := coveringBallChart b hb Γ f hf (Classical.choose (hf.surjective q))
  chart_mem_atlas q := ⟨_, rfl⟩
  mem_chart_source q := by
    rw [coveringBallChart_source]
    have h := hf.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
      (x := Classical.choose (hf.surjective q))
    change f (Classical.choose (hf.surjective q)) ∈
      (coveringBallBranch b Γ f hf (Classical.choose (hf.surjective q))).source at h
    rwa [Classical.choose_spec (hf.surjective q)] at h

theorem coveringBallAtlas_isManifold :
    @IsManifold ℂ _ ArithmeticQuotientBoostBall.BallCoordinates _ _ ArithmeticQuotientBoostBall.BallCoordinates _ 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates) 1
      Q _ (coveringBallAtlas b hb Γ f hf) := by
  let : ChartedSpace ArithmeticQuotientBoostBall.BallCoordinates Q := coveringBallAtlas b hb Γ f hf
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨z, rfl⟩ := he
  obtain ⟨z', rfl⟩ := he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id_eq, Set.range_id, Set.inter_univ]
  intro w hw
  have hwball := coveringBallChart_target_subset b hb Γ f hf z hw.1
  let u : ArithmeticQuotientBoostBall.Ball b := ⟨w, hwball⟩
  have hwsource : f u ∈ (coveringBallBranch b Γ f hf z').source := by
    have h := hw.2
    change (coveringBallChart b hb Γ f hf z).symm w ∈ (coveringBallChart b hb Γ f hf z').source at h
    rw [coveringBallChart_source, coveringBallChart_symm_apply] at h
    simpa only [show (QuotientAtlas.Arithmetic.ballInclusion b hb).symm w = u from QuotientAtlas.Arithmetic.ballInclusion_symm_coe b hb u] using h
  have hcd := QuotientAtlas.Arithmetic.quotient_branch_contDiffAt b hb Γ hf (coveringBallBranch b Γ f hf z')
    (fun _ hy => hf.isCoveringMap.isLocalHomeomorph.apply_localInverseAt_of_mem hy) u hwsource 1
  have heq : (fun x : ArithmeticQuotientBoostBall.BallCoordinates =>
      coveringBallChart b hb Γ f hf z' ((coveringBallChart b hb Γ f hf z).symm x)) =
      (fun x : ArithmeticQuotientBoostBall.BallCoordinates => (coveringBallBranch b Γ f hf z' (f ((QuotientAtlas.Arithmetic.ballInclusion b hb).symm x))).val) := by
    funext x
    rw [coveringBallChart_apply, coveringBallChart_symm_apply]
  change ContDiffWithinAt ℂ 1 (fun x =>
    coveringBallChart b hb Γ f hf z' ((coveringBallChart b hb Γ f hf z).symm x)) _ w
  rw [heq]
  exact hcd.contDiffWithinAt

lemma coveringBallProjection_submersion (z : ArithmeticQuotientBoostBall.Ball b) :
    letI : ChartedSpace ArithmeticQuotientBoostBall.BallCoordinates Q := coveringBallAtlas b hb Γ f hf
    MDifferentiableAt 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates) 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates)
      (fun w => f ((QuotientAtlas.Arithmetic.ballInclusion b hb).symm w)) z.val ∧
    Function.Surjective (mfderiv 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates) 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates)
      (fun w => f ((QuotientAtlas.Arithmetic.ballInclusion b hb).symm w)) z.val) := by
  let : ChartedSpace ArithmeticQuotientBoostBall.BallCoordinates Q := coveringBallAtlas b hb Γ f hf
  let : IsManifold 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates) 1 Q := coveringBallAtlas_isManifold b hb Γ f hf
  have hm : coveringBallChart b hb Γ f hf z ∈ atlas ArithmeticQuotientBoostBall.BallCoordinates Q := ⟨z, rfl⟩
  have hd := mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates)) hm
  have htar := coveringBallChart_target_self b hb Γ f hf z
  have he : ((coveringBallChart b hb Γ f hf z).symm : ArithmeticQuotientBoostBall.BallCoordinates → Q) =
      (fun w => f ((QuotientAtlas.Arithmetic.ballInclusion b hb).symm w)) := funext (coveringBallChart_symm_apply b hb Γ f hf z)
  exact ⟨he ▸ hd.mdifferentiableAt_symm htar, he ▸ hd.symm.mfderiv_surjective htar⟩

end

end OAI.Geometry.ComplexBall.CoveringAtlas.ArithmeticQuotient

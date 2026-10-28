import OAI.RepresentationTheory.Weil.UnitarySplitting.DualPair
import OAI.RepresentationTheory.Weil.UnitarySplitting.Weak
import OAI.RepresentationTheory.Weil.UnitarySplitting.StrongTopology

/-! # Group Topology -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.GroupTopology.Construction

noncomputable section

/-! Topological-group realization of the concrete symplectic and
oscillator groups used by UnitarySplitting. -/

open scoped BigOperators

section FiniteDimensional
variable {F V : Type} [NontriviallyNormedField F] [CompleteSpace F]
    [AddCommGroup V] [Module F V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul F V] [T2Space V] [FiniteDimensional F V]

omit [CompleteSpace F] [IsTopologicalAddGroup V] [ContinuousSMul F V]
  [T2Space V] [FiniteDimensional F V] in
theorem pairing_eval_continuous (β : V → V → F) (x : V) :
    Continuous (fun g : DualPair.Construction.pairingIsometries β => g.val x) := by
  have ho : Continuous (fun g : DualPair.Construction.pairingIsometries β =>
      ((fun x => g.val x), (fun x => g.val.symm x))) := continuous_induced_dom
  exact (continuous_apply x).comp (continuous_fst.comp ho)

omit [CompleteSpace F] [IsTopologicalAddGroup V] [ContinuousSMul F V]
  [T2Space V] [FiniteDimensional F V] in
theorem pairing_inverse_eval_continuous (β : V → V → F) (x : V) :
    Continuous (fun g : DualPair.Construction.pairingIsometries β => g.val.symm x) := by
  have ho : Continuous (fun g : DualPair.Construction.pairingIsometries β =>
      ((fun x => g.val x), (fun x => g.val.symm x))) := continuous_induced_dom
  exact (continuous_apply x).comp (continuous_snd.comp ho)

theorem pairing_joint_continuous (β : V → V → F) :
    Continuous (fun q : DualPair.Construction.pairingIsometries β × V => q.1.val q.2) := by
  let b := Module.finBasis F V
  have hb : Continuous b.equivFun := b.equivFun.toLinearMap.continuous_of_finiteDimensional
  have heq (g : DualPair.Construction.pairingIsometries β) (x : V) :
      g.val x = ∑ i, b.equivFun x i • g.val (b i) := by
    calc
      g.val x = g.val (∑ i, b.repr x i • b i) := congrArg g.val (b.sum_repr x).symm
      _ = _ := by simp only [map_sum, map_smul]; rfl
  have hsum : Continuous (fun q : DualPair.Construction.pairingIsometries β × V =>
      ∑ i, b.equivFun q.2 i • q.1.val (b i)) := by
    apply continuous_finsetSum
    intro i hi
    exact ((continuous_apply i).comp (hb.comp continuous_snd)).smul
      ((pairing_eval_continuous β (b i)).comp continuous_fst)
  exact hsum.congr (fun q => (heq q.1 q.2).symm)

theorem pairingIsometries_isTopologicalGroup (β : V → V → F) :
    IsTopologicalGroup (DualPair.Construction.pairingIsometries β) := by
  have hInv : Continuous (fun g : DualPair.Construction.pairingIsometries β => g⁻¹) := by
    apply continuous_induced_rng.mpr
    apply Continuous.prodMk
    · apply continuous_pi
      intro x
      simpa only [Subgroup.coe_inv, LinearEquiv.coe_inv] using
        pairing_inverse_eval_continuous β x
    · apply continuous_pi
      intro x
      change Continuous (fun g : DualPair.Construction.pairingIsometries β => g.val x)
      exact pairing_eval_continuous β x
  let : ContinuousInv (DualPair.Construction.pairingIsometries β) := ⟨hInv⟩
  have hProd (x : V) :
      Continuous (fun q : DualPair.Construction.pairingIsometries β × DualPair.Construction.pairingIsometries β => q.1.val (q.2.val x)) :=
    (pairing_joint_continuous β).comp
      (continuous_fst.prodMk ((pairing_eval_continuous β x).comp continuous_snd))
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · apply continuous_induced_rng.mpr
    apply Continuous.prodMk
    · apply continuous_pi
      intro x
      exact hProd x
    · apply continuous_pi
      intro x
      change Continuous (fun q : DualPair.Construction.pairingIsometries β × DualPair.Construction.pairingIsometries β =>
        q.2.val.symm (q.1.val.symm x))
      have h := (hProd x).comp
        ((continuous_inv.comp continuous_snd).prodMk (continuous_inv.comp continuous_fst))
      simpa only [Function.comp_def, Subgroup.coe_inv, LinearEquiv.coe_inv] using h
  · exact hInv

end FiniteDimensional

theorem tensorSymplectic_isTopologicalGroup
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [CompleteSpace F] [FiniteDimensional F E]
    (hF : ¬ DiscreteTopology F) (hEmbedding : Continuous (algebraMap F E))
    {m n : ℕ} (σ : E ≃ₐ[F] E)
    (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E) :
    IsTopologicalGroup (Oscillator.Construction.TensorSymplectic σ H K) := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField F with hd | ⟨_, rfl⟩
  · exact (hF hd).elim
  · let : ContinuousSMul F E := ⟨by
      have hm : Continuous (fun p : F × E => algebraMap F E p.1 * p.2) :=
        continuous_mul.comp ((hEmbedding.comp continuous_fst).prodMk continuous_snd)
      simpa only [Algebra.smul_def] using hm⟩
    exact pairingIsometries_isTopologicalGroup (DualPair.Construction.traceTensorPairing σ H K)

/-- The independently defined intertwiner group has the topological
group structure required in the UnitarySplitting target. -/
theorem circleExtension_isTopologicalGroup
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [CompleteSpace F] [LocallyCompactSpace F] [FiniteDimensional F E]
    [MeasurableSpace F] [BorelSpace F]
    (hF : ¬ DiscreteTopology F) (hEmbedding : Continuous (algebraMap F E))
    {m n : ℕ} (σ : E ≃ₐ[F] E)
    (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (ψ : AddChar F ℂ) :
    IsTopologicalGroup (Oscillator.Construction.CircleExtension σ H K c ψ) := by
  let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
  let : IsTopologicalGroup (Oscillator.Construction.TensorSymplectic σ H K) :=
    tensorSymplectic_isTopologicalGroup hF hEmbedding σ H K
  let S := Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)
  let L := MeasureTheory.Lp ℂ 2 (Weak.Construction.referencePositionMeasure F (m * n))
  let : NormedAddCommGroup S :=
    NormedAddCommGroup.induced S L (Weak.Construction.testToL2 F (m * n)) (Weak.Construction.testToL2_injective F (m * n))
  let : NormedSpace ℂ S := NormedSpace.induced ℂ S L (Weak.Construction.testToL2 F (m * n))
  let p := (Oscillator.Construction.circleProjection σ H K c ψ).toMonoidHom
  let r := Oscillator.Construction.oscillatorRepresentation σ H K c ψ
  have hr : ∀ g, Isometry (r g) := by
    intro g
    apply AddMonoidHomClass.isometry_of_norm (r g)
    intro f
    change ‖Weak.Construction.testToL2 F (m * n) (r g f)‖ = ‖Weak.Construction.testToL2 F (m * n) f‖
    rw [Weak.Construction.testToL2_norm, Weak.Construction.testToL2_norm, Oscillator.Construction.oscillatorRepresentation_unitary]
  have hdist (f h : S) : dist f h =
      Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) (f - h)) := by
    rw [dist_eq_norm]
    exact Weak.Construction.testToL2_norm F (m * n) (f - h)
  have htop : Oscillator.Construction.circleExtensionTopology σ H K c ψ =
      StrongTopology.operatorTopology p r := by
    unfold Oscillator.Construction.circleExtensionTopology StrongTopology.operatorTopology
    congr 1
    funext g
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext q
        exact (hdist (r g q.1) q.2).symm
      · funext q
        change Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy F (m * n)
            ((r g).symm q.1 - q.2)) = dist (r g⁻¹ q.1) q.2
        rw [map_inv, LinearEquiv.coe_inv]
        exact (hdist ((r g).symm q.1) q.2).symm
  change @IsTopologicalGroup _ (Oscillator.Construction.circleExtensionTopology σ H K c ψ) _
  rw [htop]
  exact StrongTopology.operator_isTopologicalGroup p r hr

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.GroupTopology.Construction

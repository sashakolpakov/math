import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.StabilizerLocalImage
import OAI.NumberTheory.ArithmeticGroups.Lattices.SubmoduleStrictDerivative

/-! # Restricted Stabilizer Local Image -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.RestrictedStabilizerLocalImage.Construction

noncomputable section

/-! Local exponential coordinates for a bilinear stabilizer inside
a multiplicatively closed linear subspace translated by the identity. -/

open scoped Classical _root_.Topology
open Filter Set _root_.ContinuousLinearMap

theorem bilinear_stabilizer_local_image_in_submodule_within
    {E L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (W : Submodule ℝ (L →L[ℝ] L))
    (hmul : ∀ X ∈ W, ∀ Y ∈ W, X * Y ∈ W)
    (f : E → (L →L[ℝ] L)) (a : E →L[ℝ] W)
    (hf0 : f 0 = 1) (hf : HasStrictFDerivAt f (W.subtypeL.comp a) 0)
    (ha : Function.Injective a)
    (hrange : a.toLinearMap.range =
      ((Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).toLinearMap.comp W.subtype).ker)
    (hfW : ∀ p, f p - 1 ∈ W)
    (hfinj : ∀ p, Function.Injective (f p))
    (hpres : ∀ p x y, f p (B x y) = B (f p x) (f p y))
    (U : Set E) (hU : U ∈ 𝓝 0) :
    ∀ᶠ Z : W in 𝓝 0,
      (∀ x y, (1 + Z.val) (B x y) = B ((1 + Z.val) x) ((1 + Z.val) y)) →
        ∃ p ∈ U, f p = 1 + Z.val := by
  let : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
  let : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
  let : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
  let : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L) := inferInstance
  let : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance
  let : NormedAddCommGroup W := inferInstance
  let : NormedSpace ℝ W := inferInstance
  let : FiniteDimensional ℝ W := inferInstance
  let D := (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).toLinearMap.comp W.subtype
  obtain ⟨V, hV⟩ := a.toLinearMap.range.exists_isCompl
  let : NormedAddCommGroup V := inferInstance
  let : NormedSpace ℝ V := inferInstance
  let : FiniteDimensional ℝ V := inferInstance
  have hdisj : Disjoint V D.ker := by rw [← hrange]; exact hV.disjoint.symm
  obtain ⟨ε, hε, hisolated⟩ := Lie.AutomorphismTransversal.Construction.quadratic_remainder_isolated_on_complement D V hdisj ‖B‖ (norm_nonneg B)
  let e : (E × V) ≃L[ℝ] W :=
    (((LinearEquiv.ofInjective a.toLinearMap ha).prodCongr (LinearEquiv.refl ℝ V)).trans
      (Submodule.prodEquivOfIsCompl _ V hV)).toContinuousLinearEquiv
  have he (p : E × V) : (e p).val = (a p.1).val + p.2.val.val := rfl
  let q : V →L[ℝ] (L →L[ℝ] L) := W.subtypeL.comp V.subtypeL
  have hPW (p : E × V) : f p.1 * (1 + q p.2) - 1 ∈ W := by
    have hid : f p.1 * (1 + q p.2) - 1 =
        (f p.1 - 1) + q p.2 + (f p.1 - 1) * q p.2 := by noncomm_ring
    rw [hid]
    exact W.add_mem (W.add_mem (hfW p.1) p.2.val.property)
      (hmul _ (hfW p.1) _ p.2.val.property)
  let P : E × V → W := fun p => ⟨f p.1 * (1 + q p.2) - 1, hPW p⟩
  have hP0 : P 0 = 0 := by
    apply Subtype.ext
    change f 0 * (1 + q 0) - 1 = 0
    rw [hf0, map_zero, add_zero, one_mul, sub_self]
  have hP : HasStrictFDerivAt P e.toContinuousLinearMap 0 := by
    apply SubmoduleStrictDerivative.Construction.hasStrictFDerivAt_submodule W P e.toContinuousLinearMap 0
    have hprod := (Bilinear.StabilizerLocalImage.Construction.hasStrictFDerivAt_product_slice f (W.subtypeL.comp a) q hf0 hf).sub_const 1
    have hder : (W.subtypeL.comp a).coprod q = W.subtypeL.comp e.toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro p
      exact (he p).symm
    rw [hder] at hprod
    exact hprod
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace V := FiniteDimensional.complete ℝ V
  have hsmall : {p : E × V | p.1 ∈ U ∧ ‖p.2.val‖ < ε} ∈ 𝓝 0 := by
    have hc : Continuous (fun p : E × V => p.2.val) := V.subtypeL.continuous.comp continuous_snd
    exact Filter.inter_mem (continuous_fst.continuousAt.preimage_mem_nhds hU)
      ((isOpen_lt hc.norm continuous_const).mem_nhds (by simpa using hε))
  have himage : P '' {p : E × V | p.1 ∈ U ∧ ‖p.2.val‖ < ε} ∈ 𝓝 0 := by
    rw [← hP0, ← hP.map_nhds_eq_of_equiv (f' := e)]
    exact Filter.image_mem_map hsmall
  filter_upwards [himage] with Z hZ
  intro hZB
  obtain ⟨p, hp, rfl⟩ := hZ
  have hPeq : 1 + (P p).val = f p.1 * (1 + q p.2) := by
    change 1 + (f p.1 * (1 + q p.2) - 1) = _
    abel
  rw [hPeq] at hZB ⊢
  have hqB : ∀ x y, (ContinuousLinearMap.id ℝ L + q p.2) (B x y) =
      B ((ContinuousLinearMap.id ℝ L + q p.2) x) ((ContinuousLinearMap.id ℝ L + q p.2) y) := by
    intro x y
    apply hfinj p.1
    rw [hpres]
    exact hZB x y
  have hq0 : p.2.val = 0 := hisolated p.2.val p.2.property hp.2
    (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect_norm_bound B (q p.2) hqB)
  have hq0' : q p.2 = 0 := congrArg Subtype.val hq0
  exact ⟨p.1, hp.1, by rw [hq0', add_zero, mul_one]⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.RestrictedStabilizerLocalImage.Construction

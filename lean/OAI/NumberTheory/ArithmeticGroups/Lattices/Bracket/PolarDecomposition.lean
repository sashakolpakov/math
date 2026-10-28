import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.BracketSquareRoot

/-! # Polar Decomposition -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.PolarDecomposition.Construction

noncomputable section

/-! In an adjoint-stable bracket automorphism group, polar
decomposition stays inside the group. -/

open _root_.ContinuousLinearMap

theorem continuousBracketChange_eq_self_iff
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (g : L ≃L[ℝ] L) :
    ContinuousBracketChange.Construction.continuousBracketChange g B = B ↔ ∀ x y, g (B x y) = B (g x) (g y) := by
  constructor
  · intro h x y
    have he := congrArg (fun C : L →L[ℝ] L →L[ℝ] L => C (g x) (g y)) h
    simpa only [ContinuousBracketChange.Construction.continuousBracketChange_apply, ContinuousLinearEquiv.symm_apply_apply] using he
  · intro h
    ext x y
    rw [ContinuousBracketChange.Construction.continuousBracketChange_apply, h, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply]

theorem bracket_automorphism_polar_decomposition
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (g : L ≃L[ℝ] L)
    (hg : ContinuousBracketChange.Construction.continuousBracketChange g B = B)
    (hadj : ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
      B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y)) :
    ∃ k s : L ≃L[ℝ] L, g = s.trans k ∧
      ContinuousBracketChange.Construction.continuousBracketChange k B = B ∧ ContinuousBracketChange.Construction.continuousBracketChange s B = B ∧
      (∀ x y, inner ℝ (k x) (k y) = inner ℝ x y) ∧ s.toLinearMap.IsSymmetric ∧
      (∀ x : L, x ≠ 0 → 0 < inner ℝ (s x) x) := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let p : L →L[ℝ] L := adjoint g.toContinuousLinearMap * g.toContinuousLinearMap
  have hsym : p.toLinearMap.IsSymmetric := by
    intro x y
    change inner ℝ (adjoint g.toContinuousLinearMap (g x)) y =
      inner ℝ x (adjoint g.toContinuousLinearMap (g y))
    rw [adjoint_inner_left, adjoint_inner_right]
    rfl
  have hpos : ∀ x : L, x ≠ 0 → 0 < inner ℝ (p x) x := by
    intro x hx
    have hgx : g x ≠ 0 := by
      intro h
      apply hx
      apply g.injective
      simpa only [map_zero] using h
    change 0 < inner ℝ (adjoint g.toContinuousLinearMap (g x)) x
    rw [adjoint_inner_left]
    change 0 < inner ℝ (g x) (g x)
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hgx)
  have hpB : ∀ x y, p (B x y) = B (p x) (p y) := by
    intro x y
    change adjoint g.toContinuousLinearMap (g (B x y)) = _
    rw [(continuousBracketChange_eq_self_iff B g).mp hg, hadj]
    rfl
  obtain ⟨s, hsSym, hsPos, hsSq, hsB⟩ := Positive.BracketSquareRoot.Construction.positive_bilinear_preserver_squareRoot B p hsym hpos hpB
  have hs : ContinuousBracketChange.Construction.continuousBracketChange s B = B := (continuousBracketChange_eq_self_iff B s).mpr hsB
  let k := s.symm.trans g
  refine ⟨k, s, ?_, CartanAutomorphism.Construction.bracketAutomorphism_trans B s.symm g (CartanAutomorphism.Construction.bracketAutomorphism_inverse B s hs) hg,
    hs, ?_, hsSym, hsPos⟩
  · ext x
    simp only [k, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_apply]
  · have hinner (x y : L) : inner ℝ (g x) (g y) = inner ℝ (s x) (s y) := by
      have hsq : s (s x) = adjoint g.toContinuousLinearMap (g x) := DFunLike.congr_fun hsSq x
      calc
        inner ℝ (g x) (g y) = inner ℝ (adjoint g.toContinuousLinearMap (g x)) y :=
          (adjoint_inner_left g.toContinuousLinearMap y (g x)).symm
        _ = inner ℝ (s (s x)) y := congrArg (fun z => inner ℝ z y) hsq.symm
        _ = inner ℝ (s x) (s y) := hsSym (s x) y
    intro x y
    change inner ℝ (g (s.symm x)) (g (s.symm y)) = _
    rw [hinner, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.PolarDecomposition.Construction

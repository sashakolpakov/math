import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.RegularWeightOrderings
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.QRChamberBound
import OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.QRBasisComparison

/-! # From Compact Split Factors -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Finite regular eigenbasis refinements turn a compact factor
before the intrinsic split diagonal into a finite-volume bound for
an ambient translated intersection. -/

open _root_.ContinuousLinearMap _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem KillingSplit.Construction.KillingSplitWeightData.inverseHaar_lt_top_of_compact_split_factors
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    [MeasurableSpace (L →L[ℝ] L)ˣ] [BorelSpace (L →L[ℝ] L)ˣ]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (hDadj : ∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint X) = 0)
    (μ : Measure (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)) [IsHaarMeasure μ]
    (Q : Set (L →L[ℝ] L)ˣ) (hQ : IsCompact Q) (x : (L →L[ℝ] L)ˣ)
    (t c : ℝ) (ht : 0 ≤ t) (T : Set (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B))
    (hfactor : ∀ g ∈ T, ∃ k : OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B, ∃ A : d.subspace,
      ∃ q ∈ Q, g.val = k.val * q * OperatorExponentialUnits.Construction.operatorExpUnit A.val)
    (hambient : ∀ g ∈ T, ∃ u ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion d.basis t c, g.val = u * x) :
    μ.inv T < ⊤ := by
  let : NormedAddCommGroup d.subspace := inferInstance
  let : NormedSpace ℝ d.subspace := inferInstance
  obtain ⟨F, hF, hRegular, hCover⟩ := Lattices.Finite.RegularWeightOrderings.Construction.finite_regular_weight_orderings (E := d.subspace) d.weight
  let J := F
  let : Finite J := hF
  let D : J → KillingSplit.Construction.KillingSplitWeightData B := fun j =>
    (d.withRegularElement hB hK j.val.2 (hRegular j.val j.property).1).reindex j.val.1
  have hOrder (j : J) : Antitone (fun i => (D j).weight i (D j).regularElement) :=
    (hRegular j.val j.property).2.2
  let b := fun j : J => (D j).basis
  have hBounds := fun j : J => Compact.QRChamberBound.Construction.compact_factor_right_chamber_qr_bound (b j) Q hQ
  choose s hs hBound using hBounds
  have hCompares := fun j : J => Ambient.QRBasisComparison.Construction.operatorQRSiegelRegion_right_translate_basis_comparison
    d.basis (b j) x t c (s j) ht
  choose C hC hCompare using hCompares
  let W : J → Set (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) :=
    fun j => {g | g.val ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion (b j) (s j) (C j)}
  have hW (j : J) : μ.inv (W j) < ⊤ :=
    (D j).qrSiegelIntersection_inverseHaar_lt_top hB hK (hOrder j) hadj hDadj μ (s j) (C j) (hs j)
  have hsub : T ⊆ ⋃ j : J, W j := by
    intro g hg
    obtain ⟨k, A, q, hq, he⟩ := hfactor g hg
    obtain ⟨j, hj, hmono⟩ := hCover A
    let j' : J := ⟨j, hj⟩
    have hexp : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix (b j').toBasis (OperatorExponentialUnits.Construction.operatorExpUnit A.val).val =
        Matrix.diagonal (fun i => Real.exp (d.weight (j.1 i) A)) :=
      (d.reindex j.1).exponential_matrix A
    have hH := hBound j' q hq k.val (OperatorExponentialUnits.Construction.operatorExpUnit A.val) (fun i => d.weight (j.1 i) A)
      (OrthogonalOperatorMatrices.Construction.orthogonalBracketUnit_matrix (b j') B k.val k.property) hexp hmono
    have hChamber : ∀ i l, i.val + 1 = l.val →
        OperatorQRVal.Construction.operatorQRLogDiagonal (b j') g.val i - OperatorQRVal.Construction.operatorQRLogDiagonal (b j') g.val l ≤ s j' := by
      intro i l hil
      rw [he]
      exact hH i l (by omega)
    obtain ⟨u, hu, hue⟩ := hambient g hg
    have hmem : g ∈ W j' := by
      change g.val ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion (b j') (s j') (C j')
      rw [hue]
      apply hCompare j' u hu
      simpa only [← hue] using hChamber
    exact Set.mem_iUnion.mpr ⟨j', hmem⟩
  apply (measure_mono hsub).trans_lt
  have hUnion := measure_biUnion_lt_top (μ := μ.inv) (s := Set.univ) (Set.toFinite (Set.univ : Set J))
    (fun j _ => hW j)
  simpa only [Set.biUnion_univ] using hUnion

end

end OAI.NumberTheory.ArithmeticGroups.Lattices

import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.BracketQRFiniteCover
import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitGroupTopology
import OAI.NumberTheory.ArithmeticGroups.Lattices.HaarFiniteCoverLattice

/-! # Conjugated Integral Bracket Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ConjugatedIntegralBracketLattice.Construction

noncomputable section

/-! Integral automorphisms of a Killing bracket form a lattice in
the self-adjoint realization, with all reduction and volume inputs derived. -/

open _root_.ContinuousLinearMap _root_.MeasureTheory _root_.MeasureTheory.Measure
open scoped OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction.Construction.BracketAction

theorem conjugatedIntegralBracketSubgroup_isLattice
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (B : L →L[ℝ] L →L[ℝ] L)
    (hint : Bilinear.DiagonalCoordinates.Construction.continuousBilinearCoordinates b.toBasis B ∈ Integral.RealCoordinates.Construction.integralRealCoordinates (Fin m × Fin m × Fin m))
    (a : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) (haB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket (a • B))
    (haK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm (a • B)).Nondegenerate)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g (a • B) = a • B →
      ∀ x y, adjoint g.toContinuousLinearMap ((a • B) x y) =
        (a • B) (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y)) :
    IntegralLattice.IsLattice (Bracket.ConjugationAction.Construction.conjugatedIntegralBracketSubgroup b (a • B) haK a) := by
  let H := UnipotentBracketGroup.Construction.continuousBracketUnitGroup (a • B)
  let Γ := Bracket.ConjugationAction.Construction.conjugatedIntegralBracketSubgroup b (a • B) haK a
  let : LocallyCompactSpace H := Bracket.UnitGroupTopology.Construction.bracketUnitGroup_locallyCompact (a • B)
  let : SecondCountableTopology H := Bracket.UnitGroupTopology.Construction.bracketUnitGroup_secondCountable (a • B)
  let : DiscreteTopology Γ := Bracket.ConjugationAction.Construction.conjugatedIntegralBracketSubgroup_discrete b (a • B) haK a
  let : MeasurableSpace (L →L[ℝ] L)ˣ := borel (L →L[ℝ] L)ˣ
  let : BorelSpace (L →L[ℝ] L)ˣ := ⟨rfl⟩
  let μ := haar (G := H)
  obtain ⟨F, hF, hcover⟩ := Integral.BracketQRFiniteCover.Construction.integral_bracket_finite_qr_cover b B hint a haB haK hadj
  let D : Set H := ⋃ f ∈ F, QRTranslateClosed.Construction.qrTranslateIntersection b (a • B) (f⁻¹ * a⁻¹).val (Real.log 2) 1
  have hD : IsClosed D := hF.isClosed_biUnion (fun f _ => QRTranslateClosed.Construction.qrTranslateIntersection_isClosed b (a • B) _ _ _)
  have hDfin : μ.inv D < ⊤ := by
    apply measure_biUnion_lt_top hF
    intro f _
    exact QRTranslateClosed.Construction.qrTranslateIntersection_inverseHaar_lt_top b (a • B) haB haK hadj μ _ _ _
      (Real.log_nonneg (by norm_num))
  apply HaarFiniteCoverLattice.Construction.lattice_of_inverseHaar_finite_cover Γ μ D hD.measurableSet hDfin
  intro g
  obtain ⟨f, hf, c, hc, γ, hγ, he⟩ := hcover g
  exact ⟨c, Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf, hc⟩⟩, γ, hγ, he⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ConjugatedIntegralBracketLattice.Construction

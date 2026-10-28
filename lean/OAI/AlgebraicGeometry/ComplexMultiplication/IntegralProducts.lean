import OAI.AlgebraicGeometry.ComplexMultiplication.AffineProducts
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Integral Products -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.IntegralProducts

noncomputable section

/-! # Integrality of the actual scheme product

Both irreducibility and reducedness are proved on actual affine product charts.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry _root_.Topology

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K)) [LocallyOfFiniteType f]

theorem integralPullbackChart (i : X.affineCover.I₀) (j : Y.affineCover.I₀)
    [Nonempty (X.affineCover.X i)] [Nonempty (Y.affineCover.X j)] :
    IsIntegral (pullback (X.affineCover.f i ≫ f) (Y.affineCover.f j ≫ g)) := by
  have : IsIntegral (X.affineCover.X i) := isIntegral_of_isOpenImmersion (X.affineCover.f i)
  have : IsIntegral (Y.affineCover.X j) := isIntegral_of_isOpenImmersion (Y.affineCover.f j)
  exact AffineProducts.affineIntegralProduct _ _

/-- The actual fibred product over an algebraically closed field is integral. -/
theorem integralSchemeProduct : IsIntegral (pullback f g) := by
  classical
  have hred : IsReduced (pullback f g) := by
    apply +allowSynthFailures @isReduced_of_isReduced_stalk
    intro z
    let i := X.affineCover.idx (pullback.fst f g z)
    let j := Y.affineCover.idx (pullback.snd f g z)
    have hi : pullback.fst f g z ∈ Set.range (X.affineCover.f i) := X.affineCover.covers _
    have hj : pullback.snd f g z ∈ Set.range (Y.affineCover.f j) := Y.affineCover.covers _
    have : Nonempty (X.affineCover.X i) := ⟨hi.choose⟩
    have : Nonempty (Y.affineCover.X j) := ⟨hj.choose⟩
    have := integralPullbackChart f g i j
    let m := pullback.map (X.affineCover.f i ≫ f) (Y.affineCover.f j ≫ g) f g
      (X.affineCover.f i) (Y.affineCover.f j) (𝟙 _) (by simp) (by simp)
    have hz : z ∈ Set.range m := by
      rw [Scheme.Pullback.range_map]
      exact ⟨hi, hj⟩
    obtain ⟨w, hw⟩ := hz
    have hstalk : _root_.IsReduced ((pullback f g).presheaf.stalk (m w)) :=
      isReduced_of_injective (m.stalkMap w).hom
        (asIso (m.stalkMap w)).commRingCatIsoToRingEquiv.injective
    exact (congrArg (fun q : ↥(pullback f g) =>
      _root_.IsReduced ((pullback f g).presheaf.stalk q)) hw).mp hstalk
  let x : X := Nonempty.some inferInstance
  let y : Y := Nonempty.some inferInstance
  let i := X.affineCover.idx x
  let j := Y.affineCover.idx y
  have hi : x ∈ Set.range (X.affineCover.f i) := X.affineCover.covers x
  have hj : y ∈ Set.range (Y.affineCover.f j) := Y.affineCover.covers y
  have : Nonempty (X.affineCover.X i) := ⟨hi.choose⟩
  have : Nonempty (Y.affineCover.X j) := ⟨hj.choose⟩
  have := integralPullbackChart f g i j
  let m := pullback.map (X.affineCover.f i ≫ f) (Y.affineCover.f j ≫ g) f g
    (X.affineCover.f i) (Y.affineCover.f j) (𝟙 _) (by simp) (by simp)
  have hdense : Dense (Set.range m) := by
    rw [Scheme.Pullback.range_map]
    exact ((X.affineCover.f i).isOpenEmbedding.isOpen_range.dense ⟨x, hi⟩).preimage
      (pullback.fst f g).isOpenMap |>.inter_of_isOpen_left
        (((Y.affineCover.f j).isOpenEmbedding.isOpen_range.dense ⟨y, hj⟩).preimage
          (pullback.snd f g).isOpenMap)
        ((X.affineCover.f i).isOpenEmbedding.isOpen_range.preimage
          (pullback.fst f g).continuous)
  have hirr : IsIrreducible (Set.range m) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ
        ↥(pullback (X.affineCover.f i ≫ f) (Y.affineCover.f j ≫ g))).image
        m m.continuous.continuousOn
  have : IrreducibleSpace ↥(pullback f g) := by
    rw [irreducibleSpace_def]
    simpa only [hdense.closure_eq, Set.top_eq_univ] using hirr.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.IntegralProducts

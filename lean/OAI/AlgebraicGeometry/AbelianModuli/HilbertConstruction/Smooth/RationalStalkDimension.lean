import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointStalkRegularParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.GeneratorHeightBound

/-! # Rational Stalk Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.RationalStalkDimension

noncomputable section

/-! A finite list of maximal-ideal generators bounds the dimension of a
Noetherian local ring. The actual smooth rational stalk therefore has
Krull dimension at most the prescribed relative dimension. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry IsLocalRing
open scoped Classical
universe u

theorem localRing_krullDim_le_maximal_generator_length
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (rs : List R) (hgen : Regular.SequenceBasic.Ideal.ofList rs = maximalIdeal R) :
    ringKrullDim R ≤ (rs.length : ℕ) := by
  have hspan : Ideal.span (rs.toFinset : Set R) = Regular.SequenceBasic.Ideal.ofList rs := by
    change Ideal.span (rs.toFinset : Set R) = Ideal.span {r | r ∈ rs}
    congr 1
    ext r
    simp only [Finset.mem_coe, List.mem_toFinset, Set.mem_ofPred_eq]
  have hm : (maximalIdeal R).height ≤ rs.toFinset.card :=
    Finite.GeneratorHeightBound.minimalPrimeHeightLeGeneratorCard (by
      rw [hspan, hgen, Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton _)
  calc
    ringKrullDim R = ((maximalIdeal R).height : WithBot ℕ∞) :=
      IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
    _ ≤ ((rs.toFinset.card : ℕ) : WithBot ℕ∞) := WithBot.coe_le_coe.mpr hm
    _ ≤ (rs.length : ℕ) := by exact_mod_cast rs.toFinset_card_le

theorem smoothRationalPoint_stalk_krullDim_le
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (g : ℕ) [SmoothOfRelativeDimension g p]
    (s : Spec (.of K) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    ringKrullDim (X.presheaf.stalk (s (IsLocalRing.closedPoint K))) ≤ (g : ℕ) := by
  have : Smooth p := SmoothOfRelativeDimension.smooth g p
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨rs, _, hgen, hlen⟩ := Rational.PointStalkRegularParameters.rationalPoint_stalk_regular_parameters p g s hs
  have h := localRing_krullDim_le_maximal_generator_length
    (X.presheaf.stalk (s (IsLocalRing.closedPoint K))) rs hgen
  simpa only [hlen] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.RationalStalkDimension

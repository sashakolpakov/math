import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.PairDifferential

/-! # Pair Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.PairCompatibility

noncomputable section

/-! A homogeneous one-chart cochain lies in the first differential kernel precisely when its sections agree on every ordered pairwise overlap. -/

universe u v w

variable {σ : Type u} [LinearOrder σ] (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M)
  [SetLike.GradedSMul (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

theorem moduleCech_one_cocycle_iff (d : ℤ) (f : HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d 1) :
    HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d 1 f = 0 ↔
      ∀ i j : σ, i < j → PairDifferential.moduleCechPairRestrictionLeft R M i j (f.val {i}) =
        PairDifferential.moduleCechPairRestrictionRight R M i j (f.val {j}) := by
  constructor
  · intro hf i j hij
    have hz : HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f.val {i, j} = 0 :=
      congrArg (fun z : HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d 2 => z.val {i, j}) hf
    rw [PairDifferential.moduleCechDifferential_pair R M f.val hij] at hz
    exact (sub_eq_zero.mp hz).symm
  · intro h
    apply Subtype.ext
    funext s
    by_cases hs : s.card = 2
    · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hs
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact (PairDifferential.moduleCechDifferential_pair R M f.val hij).trans
          (sub_eq_zero.mpr (h i j hij).symm)
      · have he : HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f.val {j, i} = 0 :=
          (PairDifferential.moduleCechDifferential_pair R M f.val hji).trans (sub_eq_zero.mpr (h j i hji).symm)
        exact (congrArg (fun t : Finset σ => HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f.val t = 0)
          (Finset.pair_comm j i)).mp he
    · exact HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech.moduleCechDifferential_card R M 1 f.val f.property.2 s hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.PairCompatibility

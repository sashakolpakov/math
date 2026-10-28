import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormSectionAffine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerStability

/-! # Ample Norm -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AmpleNorm.Construction

noncomputable section

/-! Whole-fiber affine section neighborhoods on the source produce
ample powers on the actual quotient by taking their constructed norms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem quotient_isAmple_of_fiber_sections
    {H S R X Y : Scheme.{u}} [IsAffine H] [IsAffine S]
    (q : X ⟶ Y) [IsFinite q] [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    (s t : R ⟶ X) (hk : IsKernelPair q s t)
    (h : H ⟶ S) [IsFinite h] (a : X ⟶ S) (r : R ⟶ H)
    (hs : IsPullback r s h a) {ι : Type v} [Fintype ι]
    (b : letI := h.appTop.hom.toAlgebra; Module.Basis ι Γ(S, ⊤) Γ(H, ⊤))
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (d : ℕ) (hdegree : ∀ y : Y, q.finrank y = d)
    (hX : IsCompact (Set.univ : Set X))
    (hsections : ∀ y : Y, ∃ (n : ℕ) (_ : 0 < n)
      (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ ((L.tensorPower n).pullback q).sheaf),
      (∀ x : X, q x = y → x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z) ∧
        IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z)) : L.IsAmple := by
  apply L.isAmple_iff_tensorPower.mpr
  refine ⟨?_, fun y => ?_⟩
  · have himage : q '' (Set.univ : Set X) = Set.univ :=
      Set.image_univ.trans q.surjective.range_eq
    exact himage ▸ hX.image q.continuous
  · obtain ⟨n, hn, z, hy, hz⟩ := hsections y
    have hd : 0 < d := (congrArg (fun n => 0 < n) (hdegree y)).mp (NormRankBasis.Construction.finiteFlat_surjective_rank_pos q y)
    let w := GlobalNormSection.Construction.finiteFlatNormSection q (L.tensorPower n) d hdegree z
    have hw : y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing w :=
      (GlobalNormSection.Construction.finiteFlatNormSection_mem_nonvanishing q (L.tensorPower n) d hdegree z y).mpr hy
    have hwA : IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing w) :=
      NormSectionAffine.Construction.finiteFlatNormSection_isAffineOpen q s t hk h a r hs b (L.tensorPower n) d hdegree z hz
    let w' := w ≫ (L.tensorPowerComposeIso d n).inv
    have hD : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing w' = AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing w :=
      AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso w (L.tensorPowerComposeIso d n).symm
    exact ⟨d * n, Nat.mul_pos hd hn, w',
      (congrArg (fun U : Y.Opens => y ∈ U) hD).mpr hw, (congrArg IsAffineOpen hD).mpr hwA⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AmpleNorm.Construction

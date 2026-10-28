import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralAffineMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RangeCriterion

/-! # Affine Range Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AffineRangeConstants

noncomputable section

/-! A map from a proper integral scheme over an algebraically closed field is constant when its image lies in one affine open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}

theorem properIntegral_map_constant_of_affine_range (p : X ⟶ Spec (.of K))
    [IsIntegral X] [UniversallyClosed p] (f : X ⟶ Y) (U : Y.Opens) (hU : IsAffineOpen U)
    (hf : f ⁻¹ᵁ U = ⊤) : ∃ a : Spec (.of K) ⟶ Y, p ≫ a = f := by
  have hr : Set.range f ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact (Open.RangeCriterion.range_subset_open_iff_preimage_eq_top f U).mpr hf
  let q := IsOpenImmersion.lift U.ι f hr
  have : IsAffine U.toScheme := hU
  obtain ⟨a, ha, _⟩ := IntegralAffineMaps.properIntegral_affineFactorization p q
  exact ⟨a ≫ U.ι, (Category.assoc _ _ _).symm.trans
    ((congrArg (fun b => b ≫ U.ι) ha).trans (IsOpenImmersion.lift_fac _ _ _))⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AffineRangeConstants

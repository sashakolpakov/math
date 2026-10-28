import OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeDimensionBound
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportDimension

/-! # Dimension Bound -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.DimensionBound.BundleCycles

noncomputable section

/-!
# LineBundleCycles: point coheight plus support dimension is at most ambient dimension
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem coheight_add_pointDimension_le (x : X) :
    coheight x + (Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f : ℕ∞) ≤
      (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f : ℕ∞) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let x' : U := ⟨x, hx⟩
  let : Nonempty U := ⟨x'⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U hU
  let p := hU.primeIdealOf x'
  have h := PrimeDimensionBound.BundleCycles.finiteType_primeHeight_add_trdeg_le ℂ Γ(X, U) p.asIdeal
  have hh : p.asIdeal.height = coheight x := by
    have h₁ : p.asIdeal.height = coheight (show Spec Γ(X, U) from p) :=
      idealHeight_eq_coheight Γ(X, U) (show Spec Γ(X, U) from p)
    have h₂ : coheight (hU.fromSpec (show Spec Γ(X, U) from p)) =
        coheight (show Spec Γ(X, U) from p) := coheight_eq_of_isOpenImmersion hU.fromSpec
    have h₃ : hU.fromSpec (show Spec Γ(X, U) from p) = x := hU.fromSpec_primeIdealOf x'
    exact h₁.trans (h₂.symm.trans (congrArg coheight h₃))
  have hs := SupportDimension.BundleCycles.pointClosure_dimension_eq_affine f x ⟨U, hU⟩ hx
  have ha := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections f U hU
  rw [hh, ← hs, ← ha] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.DimensionBound.BundleCycles

import OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeDimensionBound
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportDimension

/-! # Codimension One Dimension Converse -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.CodimensionOneDimensionConverse.BundleCycles

noncomputable section

/-! # LineBundleCycles: a one-dimensional transcendence drop characterizes a codimension-one prime support -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

theorem primeHeight_one_of_transcendence_drop (K A : Type) [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (p : Ideal A) [p.IsPrime]
    (h : (Algebra.trdeg K (A ⧸ p)).toNat + 1 = (Algebra.trdeg K A).toNat) : p.height = 1 := by
  have hb := PrimeDimensionBound.BundleCycles.primeHeight_add_quotient_dimension_le p
  rw [DivisorClass.Chern.FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg K A,
    DivisorClass.Chern.FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg K (A ⧸ p), ← h,
    Nat.cast_add, Nat.cast_one, add_comm _ (1 : WithBot ℕ∞)] at hb
  have hp : p.height ≤ 1 := WithBot.coe_le_coe.mp (ENat.WithBot.add_le_add_natCast_right_iff.mp hb)
  have hn : p ≠ ⊥ := by
    intro he
    rw [he, (AlgEquiv.quotientBot K A).trdeg_eq] at h
    omega
  exact le_antisymm hp (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hn))

theorem pointCoheight_one_of_dimension_drop {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (x : X)
    (h : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f) :
    coheight x = 1 := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let x' : U := ⟨x, hxU⟩
  let : Nonempty U := ⟨x'⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U hU
  let p := hU.primeIdealOf x'
  have hs := Point.SupportDimension.BundleCycles.pointClosure_dimension_eq_affine f x ⟨U, hU⟩ hxU
  have ha := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections f U hU
  have hd : (Algebra.trdeg ℂ (Γ(X, U) ⧸ p.asIdeal)).toNat + 1 = (Algebra.trdeg ℂ Γ(X, U)).toNat := by
    rw [← hs, ← ha]
    exact h
  have hp := primeHeight_one_of_transcendence_drop ℂ Γ(X, U) p.asIdeal hd
  have h₁ : p.asIdeal.height = coheight (show Spec Γ(X, U) from p) :=
    idealHeight_eq_coheight Γ(X, U) (show Spec Γ(X, U) from p)
  have h₂ : coheight (hU.fromSpec (show Spec Γ(X, U) from p)) = coheight (show Spec Γ(X, U) from p) :=
    coheight_eq_of_isOpenImmersion hU.fromSpec
  have h₃ : hU.fromSpec (show Spec Γ(X, U) from p) = x := hU.fromSpec_primeIdealOf x'
  exact (congrArg coheight h₃).symm.trans (h₂.trans (h₁.symm.trans hp))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.CodimensionOneDimensionConverse.BundleCycles

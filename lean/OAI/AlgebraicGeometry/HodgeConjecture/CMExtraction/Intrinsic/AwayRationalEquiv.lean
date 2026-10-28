import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayFaithful

/-! # Away Rational Equiv -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayRationalEquiv

noncomputable section

/-! Faithfulness identifies the actual residual range with its rational
unitary source. This permits transport of genuine away local structures. -/

open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
  (hu : FiniteDilation.NativeFiniteCoordinateIdentity E D e u)

def nativeAwayRationalEquiv : D.RationalSU ≃* RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu :=
  MulEquiv.ofBijective (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeAway E D hg hμ v hv e he c u hu)
    ⟨AwayFaithful.nativeAway_injective E D hg hμ v hv e he c u hu, by
      intro a
      obtain ⟨g, hg'⟩ := a.property
      exact ⟨g, Subtype.ext hg'⟩⟩

theorem nativeAwayRationalEquiv_apply (g : D.RationalSU) :
    nativeAwayRationalEquiv E D hg hμ v hv e he c u hu g =
      RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeAway E D hg hμ v hv e he c u hu g := rfl

theorem nativeAwayRationalEquiv_symm_apply (g : D.RationalSU) :
    (nativeAwayRationalEquiv E D hg hμ v hv e he c u hu).symm
        (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeAway E D hg hμ v hv e he c u hu g) = g :=
  (nativeAwayRationalEquiv E D hg hμ v hv e he c u hu).symm_apply_apply g

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AwayRationalEquiv

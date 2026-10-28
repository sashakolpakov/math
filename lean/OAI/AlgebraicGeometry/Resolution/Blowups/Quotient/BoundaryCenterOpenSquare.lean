import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.ModeledBoundaryCenterLift

/-! # Boundary Center Open Square -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.BoundaryCenterOpenSquare.Construction

noncomputable section

/-! Transfer the quotient-model center lift through a specified actual ambient open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem quotient_boundary_center_lift_on_open_square
    {k : Type u} [Field k] (R A : CommRingCat.{u}) {T : Type u} [CommRing T]
    [Algebra k R] [Algebra k A] [Algebra k T] [Algebra.Smooth k R]
    (f : R →ₐ[k] A) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    (q : A →ₐ[k] T) (hq : Function.Surjective q) (z : R)
    (hker : RingHom.ker q.toRingHom = Ideal.span {f z})
    (D : Derivation k R R) (hDz : D z = 1)
    {β : Type v} [Fintype β] (w : β → R) (I : Ideal R)
    (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k T β (fun j => q (f (w j)))) (C : Finset M.indices)
    (F : Finset β) (hF : ∀ j, j ∈ F ↔ ∃ i ∈ C, M.coordinate j = some i)
    (hI : I.map f.toRingHom = ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map).comap q.toRingHom)
    (p : PrimeSpectrum R) (hzp : z ∈ p.asIdeal)
    (P : PrimeSpectrum A) (hP : PrimeSpectrum.comap f.toRingHom P = p) :
    Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w F p) := by
  have hf : f.toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom f.toRingHom)).mp inferInstance
  let : Algebra.Smooth k A := Blowups.Etale.RefinementHelpers.Construction.smooth_target_of_etale_algHom k f hf
  let D' : Derivation k A A := Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k f.toRingHom hf f.commutes D
  have hD' : D' (f z) = 1 := by
    change Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k f.toRingHom hf f.commutes D (f.toRingHom z) = 1
    rw [Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom_apply, hDz, map_one]
  have hzP : f z ∈ P.asIdeal := by
    change z ∈ P.asIdeal.comap f.toRingHom
    have he : P.asIdeal.comap f.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hP
    rw [he]
    exact hzp
  obtain ⟨L⟩ := ModeledBoundaryCenterLift.Construction.quotient_modeled_boundary_center_lifts_to_open A q hq (f z) hker D' hD'
    (fun j => f (w j)) M C F hF P hzP
  have L' : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k A (I.map f.toRingHom)
      (fun j => f (w j)) F P := hI.symm ▸ L
  exact ⟨L'.comp I w F f p hP⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.BoundaryCenterOpenSquare.Construction

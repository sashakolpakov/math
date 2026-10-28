import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.IsoChartRecovery

/-! # Represented Polarized Iso Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedPolarizedIsoFiniteness

noncomputable section

/-! Local quasi-projective isomorphism parameters make every representation of the full polarized-isomorphism functor finite type over its locally Noetherian base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem representedPolarizedIsoParameter_finiteType
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (M : Over S) (e : Family.LevelIsoFunctor.familyLevelIsoFunctor A B ≅ yoneda.obj M) :
    LocallyOfFiniteType M.hom ∧ QuasiCompact M.hom := by
  let : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFiniteType.{u}) (Q := RingHom.FiniteType)
  let : IsZariskiLocalAtTarget (@QuasiCompact.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  let C := fun x : S => Polarized.IsoOpenChart.polarizedIsoOpenChart A B hδ hN x
  have hcover : ∀ x : S, ∃ a y, (C a).inclusion y = x := by
    intro x
    obtain ⟨y, hy⟩ := (C x).covers
    exact ⟨x, y, hy⟩
  let U : Scheme.OpenCover S := by
    have (x : S) : IsOpenImmersion (C x).inclusion := (C x).openImmersion
    exact Scheme.Cover.mkOfCovers S (fun x => (C x).base) (fun x => (C x).inclusion) hcover
  constructor
  · apply (IsZariskiLocalAtTarget.iff_of_openCover
      (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u})) U).mpr
    intro x
    exact (C x).pullback_locallyOfFiniteType M e
  · apply (IsZariskiLocalAtTarget.iff_of_openCover
      (P := (@QuasiCompact : MorphismProperty Scheme.{u})) U).mpr
    intro x
    exact (C x).pullback_quasiCompact M e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedPolarizedIsoFiniteness

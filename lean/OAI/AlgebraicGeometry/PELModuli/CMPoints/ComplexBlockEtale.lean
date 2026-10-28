import OAI.AlgebraicGeometry.PELModuli.CMPoints.FiniteGroupPresentation
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale

/-! # Complex Block Etale -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexBlockEtale

noncomputable section

/-! Every positive-level complex torsion scheme is finite etale by
the checked TorsionQuotient theorem. Closed projector blocks are finite etale too. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem complex_stalk_natCast_isUnit (N : ℕ) [NeZero N]
    (x : Spec (.of ℂ)) :
    IsUnit (N : (Spec (.of ℂ)).presheaf.stalk x) := by
  let f := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
    (Spec (.of ℂ)).presheaf.germ ⊤ x trivial
  have h : IsUnit (N : ℂ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne N))
  simpa only [map_natCast] using h.map f.hom

theorem complex_torsion_finite_etale {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of ℂ))) (N : ℕ) [NeZero N] :
    IsFinite (BlocksProjectors.torsionScheme A N).hom ∧ Etale (BlocksProjectors.torsionScheme A N).hom :=
  AbelianScheme.TorsionQuotient.Etale.TorsionEtale.torsion_finite_etale A.scheme N (complex_stalk_natCast_isUnit N)

theorem complex_idempotent_block_finite_etale {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of ℂ))) {O : Type} [CommRing O]
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (N : ℕ) [NeZero N] (a : O) :
    IsFinite (BlocksProjectors.idempotentBlockScheme A ρ N a).hom ∧ Etale (BlocksProjectors.idempotentBlockScheme A ρ N a).hom := by
  obtain ⟨hf, he⟩ := complex_torsion_finite_etale A N
  let : IsFinite (BlocksProjectors.torsionScheme A N).hom := hf
  let : Etale (BlocksProjectors.torsionScheme A N).hom := he
  let i := equalizer.ι (BlocksProjectors.torsionInclusion A N ≫ ρ.map a) (BlocksProjectors.torsionInclusion A N)
  let : IsClosedImmersion i.left := isClosedImmersion_equalizer_ι_left _ _
  have hfinite : IsFinite (BlocksProjectors.idempotentBlockScheme A ρ N a).hom := by
    rw [← i.w]
    infer_instance
  let : IsFinite (BlocksProjectors.idempotentBlockScheme A ρ N a).hom := hfinite
  let : FormallyUnramified (BlocksProjectors.idempotentBlockScheme A ρ N a).hom := by
    rw [← i.w]
    exact MorphismProperty.comp_mem (@FormallyUnramified) _ _ inferInstance inferInstance
  let : IsLocallyNoetherian (Spec (.of ℂ)) := inferInstance
  let : LocallyOfFinitePresentation (BlocksProjectors.idempotentBlockScheme A ρ N a).hom := inferInstance
  exact ⟨hfinite, Etale.of_formallyUnramified_of_flat _⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexBlockEtale

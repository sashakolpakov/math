import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ProjectiveAffineNeighborhoods
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.PolarizationEmbedding
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Affine Family Neighborhoods -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AffineFamilyNeighborhoods

noncomputable section

section

/-! The total space of an actual polarized family over an affine
noetherian algebra over an infinite field has affine neighborhoods of
every finite set. Its projective embedding is constructed from the
canonical polarization line. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem affine_polarized_family_finite_set_affine_neighborhood
    {K : Type} [Field K] [Infinite K] {S : Scheme.{0}} [IsAffine S]
    [Algebra K Γ(S, ⊤)] [IsNoetherianRing Γ(S, ⊤)]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (F : Set A.abelian.scheme.left) (hF : F.Finite) :
    ∃ V : A.abelian.scheme.left.Opens, IsAffineOpen V ∧ F ⊆ V := by
  obtain ⟨_, _, L, _, n, s, hs, hi⟩ := Affine.PolarizationEmbedding.polarized_exists_affine_section_embedding A
  let i := AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs
  let p := pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ
  have : IsClosedImmersion i.left := hi
  have : IsIso p := inferInstanceAs (IsIso
    (pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ))
  have : IsClosedImmersion p := inferInstance
  have : IsClosedImmersion (i.left ≫ p) := inferInstance
  exact Relative.ProjectiveAffineNeighborhoods.finite_set_affine_neighborhood_of_relative_projective_embedding (K := K)
    n (i.left ≫ p) F hF

end

/-! A polarized family's total space inherits affine neighborhoods of
finite sets from its noetherian base over an infinite field. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem polarized_family_finite_set_affine_neighborhood
    {K : Type} [Field K] [Infinite K] {S : Scheme.{0}} [IsLocallyNoetherian S]
    (b : S ⟶ Spec (.of K))
    (hS : ∀ F : Set S, F.Finite → ∃ V : S.Opens, IsAffineOpen V ∧ F ⊆ V)
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (F : Set A.abelian.scheme.left) (hF : F.Finite) :
    ∃ V : A.abelian.scheme.left.Opens, IsAffineOpen V ∧ F ⊆ V := by
  let a := A.abelian.scheme.hom
  obtain ⟨U, hU, hFU⟩ := hS (a '' F) (hF.image a)
  have : IsAffine U.toScheme := hU
  have : IsNoetherianRing Γ(U.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.toScheme⟩
  let : Algebra K Γ(U.toScheme, ⊤) :=
    (((Scheme.ΓSpecIso (.of K)).inv ≫ (U.ι ≫ b).appTop).hom).toAlgebra
  let p := pullback.fst a U.ι
  have : IsOpenImmersion p := inferInstanceAs (IsOpenImmersion (pullback.fst a U.ι))
  have hF' : (p ⁻¹' F).Finite := Set.Finite.preimage p.injective.injOn hF
  obtain ⟨V, hV, hFV⟩ := affine_polarized_family_finite_set_affine_neighborhood (K := K)
    (A.pullback U.ι) (p ⁻¹' F) hF'
  have : IsAffine V.toScheme := hV
  let j := V.ι ≫ p
  have : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (V.ι ≫ p))
  refine ⟨j.opensRange, isAffineOpen_opensRange j, ?_⟩
  intro x hx
  have hxU : a x ∈ U := hFU ⟨x, hx, rfl⟩
  have hxrange : x ∈ Set.range p := by
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    exact hxU
  obtain ⟨y, hy⟩ := hxrange
  have hyV : y ∈ V := hFV (show p y ∈ F from hy.symm ▸ hx)
  exact ⟨⟨y, hyV⟩, hy⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AffineFamilyNeighborhoods

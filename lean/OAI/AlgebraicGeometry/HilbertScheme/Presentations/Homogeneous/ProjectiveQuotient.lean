import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.Quotient
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Projective Quotient -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ProjectiveQuotient.HomogeneousQuotient

noncomputable section

/-!
The projective spectrum of a homogeneous quotient is a closed subscheme
of the original projective spectrum. On every projective basic open, its inclusion comes
from a surjective map of homogeneous localizations.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

universe u v

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜]

def projectiveQuotient (I : HomogeneousIdeal (𝒜)) : Scheme :=
  Proj (Quotient.HomogeneousQuotient.quotientGrading I)

def projectiveQuotientInclusion (I : HomogeneousIdeal (𝒜)) :
    projectiveQuotient I ⟶ Proj (𝒜) :=
  Proj.map (Quotient.HomogeneousQuotient.gradedQuotientMap I) (Quotient.HomogeneousQuotient.irrelevant_quotient_le_map I)

theorem quotient_away_map_surjective (I : HomogeneousIdeal (𝒜))
    {d : ℕ} (s : A) (hs : s ∈ 𝒜 d) :
    Function.Surjective (HomogeneousLocalization.Away.map (Quotient.HomogeneousQuotient.gradedQuotientMap I) s) := by
  intro z
  obtain ⟨m, q, hq, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (Quotient.HomogeneousQuotient.quotientGrading I)
    ((Quotient.HomogeneousQuotient.gradedQuotientMap I).map_mem hs) z
  obtain ⟨f, hf, rfl⟩ := hq
  refine ⟨HomogeneousLocalization.Away.mk (𝒜) hs m f hf, ?_⟩
  rw [HomogeneousLocalization.Away.map_mk]
  rfl

theorem projectiveQuotientInclusion_restrict_closed (I : HomogeneousIdeal (𝒜))
    {d : ℕ} (hd : 0 < d) (s : A) (hs : s ∈ 𝒜 d) :
    IsClosedImmersion (projectiveQuotientInclusion I ∣_ Proj.basicOpen (𝒜) s) := by
  let f := Quotient.HomogeneousQuotient.gradedQuotientMap I
  let src := Proj.basicOpenIsoSpec (Quotient.HomogeneousQuotient.quotientGrading I) (f s) (f.map_mem hs) hd
  let tgt := Proj.basicOpenIsoSpec (𝒜) s hs hd
  let a := Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f s))
  have ha : IsClosedImmersion a := IsClosedImmersion.spec_of_surjective _
    (quotient_away_map_surjective I s hs)
  have hdiag : src.inv ≫ (projectiveQuotientInclusion I ∣_ Proj.basicOpen (𝒜) s) =
      a ≫ tgt.inv := by
    apply (cancel_mono (Proj.basicOpen (𝒜) s).ι).mp
    erw [Category.assoc, morphismRestrict_ι]
    exact Proj.awayι_comp_map f (Quotient.HomogeneousQuotient.irrelevant_quotient_le_map I) hd s hs
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    src.inv (projectiveQuotientInclusion I ∣_ Proj.basicOpen (𝒜) s)).mp
  rw [hdiag]
  exact IsClosedImmersion.comp a tgt.inv

instance projectiveQuotientInclusion_isClosedImmersion (I : HomogeneousIdeal (𝒜)) :
    IsClosedImmersion (projectiveQuotientInclusion I) := by
  let A := 𝒜
  let Index := Σ d : PNat, A d
  let U (s : Index) := Proj.basicOpen A s.2.val
  have hcover : iSup U = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top
    apply (HomogeneousIdeal.toIdeal_irrelevant_le A).mpr
    intro d hd f hf
    exact Ideal.subset_span ⟨(⟨⟨d, hd⟩, ⟨f, hf⟩⟩ : Index), rfl⟩
  apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) U hcover).mpr
  intro s
  exact projectiveQuotientInclusion_restrict_closed I s.1.property s.2.val s.2.property

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ProjectiveQuotient.HomogeneousQuotient

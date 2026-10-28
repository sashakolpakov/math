import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.EtaleDetection
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Agreement Locus -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AgreementLocus.Construction

/-!
The block condition on a finite etale universal subgroup is represented
by a clopen locus in the parameter scheme. This supplies finite etaleness
of the restriction, not merely representability by an open subscheme.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

section EqualityLocus

variable {S : Scheme.{u}} {X H Y : Over S}

/-- A morphism equalizes two maps to an etale target precisely when its
image lies in their scheme-theoretic equalizer. -/
theorem equalizes_iff_range_subset
    [Etale Y.hom] (f g : H ⟶ Y) (w : X ⟶ H) :
    w ≫ f = w ≫ g ↔
      Set.range w.left ⊆ Set.range (equalizer.ι f g).left := by
  have : IsOpenImmersion (equalizer.ι f g).left := EtaleDetection.Construction.equalizer_openImmersion f g
  constructor
  · intro h
    rintro _ ⟨x, rfl⟩
    refine ⟨(equalizer.lift w h).left x, ?_⟩
    change ((equalizer.lift w h).left ≫ (equalizer.ι f g).left) x = w.left x
    rw [← Over.comp_left, equalizer.lift_ι]
  · intro h
    let l := IsOpenImmersion.lift (equalizer.ι f g).left w.left h
    have hl : l ≫ (equalizer.ι f g).left = w.left := IsOpenImmersion.lift_fac _ _ h
    apply Over.OverMorphism.ext
    change w.left ≫ f.left = w.left ≫ g.left
    rw [← hl, Category.assoc, Category.assoc]
    exact congrArg (fun a => l ≫ a.left) (equalizer.condition f g)

end EqualityLocus

variable {S : Scheme.{u}} {P H Y : Over S}

/-- Parameters at which the two maps agree on the whole finite fiber. -/
def agreementSet (p : H ⟶ P) (f g : H ⟶ Y) : Set P.left :=
  (p.left '' (Set.range (equalizer.ι f g).left)ᶜ)ᶜ

theorem agreementSet_isClopen
    (p : H ⟶ P) [IsFinite p.left] [Etale p.left]
    [Etale Y.hom] [IsSeparated Y.hom] (f g : H ⟶ Y) :
    IsClopen (agreementSet p f g) := by
  have : IsOpenImmersion (equalizer.ι f g).left := EtaleDetection.Construction.equalizer_openImmersion f g
  have hopen : IsOpen (Set.range (equalizer.ι f g).left) :=
    (equalizer.ι f g).left.isOpenEmbedding.isOpen_range
  have hclosed : IsClosed (Set.range (equalizer.ι f g).left) :=
    (equalizer.ι f g).left.isClosedEmbedding.isClosed_range
  constructor
  · exact (p.left.isOpenMap _ hclosed.isOpen_compl).isClosed_compl
  · exact (p.left.isClosedMap _ hopen.isClosed_compl).isOpen_compl

/-- The relative pullback has the expected image on underlying points. -/
theorem range_relative_pullback_fst
    {T : Over S} (p : H ⟶ P) (b : T ⟶ P) :
    Set.range (pullback.fst p b).left = p.left ⁻¹' Set.range b.left := by
  have h := ((IsPullback.of_hasPullback p b).map (Over.forget S)).flip
  have hr := Scheme.image_preimage_eq_of_isPullback h (Set.univ : Set T.left)
  change (pullback.fst p b).left '' ((pullback.snd p b).left ⁻¹' Set.univ) =
    p.left ⁻¹' (b.left '' Set.univ) at hr
  simpa only [Set.preimage_univ, Set.image_univ] using hr

/-- The agreement locus has the required universal property under
arbitrary base change, including nonreduced parameter schemes. -/
theorem factors_through_agreement_iff
    [Etale Y.hom] (p : H ⟶ P) (f g : H ⟶ Y)
    {T : Over S} (b : T ⟶ P) :
    Set.range b.left ⊆ agreementSet p f g ↔
      pullback.fst p b ≫ f = pullback.fst p b ≫ g := by
  rw [equalizes_iff_range_subset, range_relative_pullback_fst]
  constructor
  · intro hb h hh
    obtain ⟨t, ht⟩ := hh
    by_contra hbad
    have hgood := hb ⟨t, rfl⟩
    exact hgood ⟨h, hbad, ht.symm⟩
  · intro hh y hy hbad
    obtain ⟨h, hbad, hp⟩ := hbad
    apply hbad
    apply hh
    change p.left h ∈ Set.range b.left
    rw [hp]
    exact hy

/-- The block equation cuts out a finite etale open subscheme of the
parameter scheme. Thus the subgroup restriction retains finiteness. -/
theorem finite_etale_agreement_locus
    (p : H ⟶ P) [IsFinite p.left] [Etale p.left]
    [Etale Y.hom] [IsSeparated Y.hom] (f g : H ⟶ Y) :
    ∃ U : P.left.Opens,
      IsFinite U.ι ∧ Etale U.ι ∧
      ∀ (T : Over S) (b : T ⟶ P),
        (∀ t : T.left, b.left t ∈ U) ↔
          pullback.fst p b ≫ f = pullback.fst p b ≫ g := by
  have hclopen := agreementSet_isClopen p f g
  let U : P.left.Opens := ⟨agreementSet p f g, hclopen.2⟩
  have hclosed : IsClosed (Set.range U.ι) := by
    rw [Scheme.Opens.range_ι]
    exact hclopen.1
  have : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι hclosed
  refine ⟨U, inferInstance, inferInstance, ?_⟩
  intro T b
  change (∀ t : T.left, b.left t ∈ agreementSet p f g) ↔ _
  simpa only [Set.range_subset_iff] using factors_through_agreement_iff p f g b

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AgreementLocus.Construction

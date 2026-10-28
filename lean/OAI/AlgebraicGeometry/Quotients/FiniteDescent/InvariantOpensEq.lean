import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Quotient

/-! # Invariant Opens Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantOpensEq.Construction.InvariantOpens

/-!
# Invariant opens of a scheme quotient

For a faithfully flat quasi-compact quotient with its scheme-theoretic kernel
pair, invariant open subsets descend uniquely to open subsets of the quotient.
These opens provide the overlaps for gluing affine quotient charts.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R X Q : Scheme.{u}} {s t : R ⟶ X} (q : X ⟶ Q)

/-- A subset invariant under the scheme-theoretic kernel pair is saturated
for the underlying quotient map. -/
theorem preimage_image_eq (h : IsKernelPair q s t) (W : Set X)
    (hW : s ⁻¹' W = t ⁻¹' W) : q ⁻¹' (q '' W) = W := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, hxy⟩
    obtain ⟨r, hr₁, hr₂⟩ := Scheme.exists_preimage_of_isPullback h y x hxy
    have hr : r ∈ s ⁻¹' W := by simpa only [Set.mem_preimage, hr₁] using hy
    rw [hW] at hr
    simpa only [Set.mem_preimage, hr₂] using hr
  · intro x hx
    exact ⟨x, hx, rfl⟩

variable [Flat q] [QuasiCompact q] [Surjective q]

/-- The image of an invariant open is open because a flat quasi-compact
surjective morphism is a quotient map of topological spaces. -/
theorem isOpen_image (h : IsKernelPair q s t) (W : X.Opens)
    (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) : IsOpen (q '' (W : Set X)) := by
  apply (Flat.isQuotientMap_of_surjective q).isOpen_preimage.mp
  rw [preimage_image_eq q h (W : Set X) (congrArg (fun V : R.Opens => (V : Set R)) hW)]
  exact W.isOpen

/-- An invariant open of the source determines an open of the quotient. -/
def descend (h : IsKernelPair q s t) (W : X.Opens) (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) :
    Q.Opens := ⟨q '' (W : Set X), isOpen_image q h W hW⟩

/-- Pulling the descended open back recovers the original invariant open. -/
theorem preimage_descend (h : IsKernelPair q s t) (W : X.Opens)
    (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) : q ⁻¹ᵁ descend q h W hW = W := by
  apply SetLike.coe_injective
  exact preimage_image_eq q h (W : Set X) (congrArg (fun V : R.Opens => (V : Set R)) hW)

/-- The descended open is unique. -/
theorem descend_unique (h : IsKernelPair q s t) (W : X.Opens)
    (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) (V : Q.Opens) (hV : q ⁻¹ᵁ V = W) :
    V = descend q h W hW := by
  apply SetLike.coe_injective
  change (V : Set Q) = q '' (W : Set X)
  rw [← hV]
  exact (Set.image_preimage_eq _ q.surjective).symm

/-- The quotient map restricted to an invariant open and its descended open. -/
noncomputable def restrictProjection (h : IsKernelPair q s t) (W : X.Opens)
    (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) : W.toScheme ⟶ (descend q h W hW).toScheme :=
  (X.isoOfEq (preimage_descend q h W hW)).inv ≫ q ∣_ descend q h W hW

instance restrictProjection_flat (h : IsKernelPair q s t) (W : X.Opens)
    (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) : Flat (restrictProjection q h W hW) := by
  unfold restrictProjection
  infer_instance

instance restrictProjection_quasiCompact (h : IsKernelPair q s t) (W : X.Opens)
    (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) : QuasiCompact (restrictProjection q h W hW) := by
  unfold restrictProjection
  infer_instance

/-- Restricting the quotient to an invariant open commutes with the inclusions. -/
@[reassoc (attr := simp)]
theorem restrictProjection_ι (h : IsKernelPair q s t) (W : X.Opens)
    (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) :
    restrictProjection q h W hW ≫ (descend q h W hW).ι = W.ι ≫ q := by
  simp [restrictProjection]

/-- The restricted quotient is the base change along the descended open immersion. -/
theorem restrictProjection_isPullback (h : IsKernelPair q s t) (W : X.Opens)
    (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) :
    IsPullback (restrictProjection q h W hW) W.ι (descend q h W hW).ι q := by
  refine (isPullback_morphismRestrict q (descend q h W hW)).of_iso
    (X.isoOfEq (preimage_descend q h W hW)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (by simp) (by simp)
  · simp [restrictProjection]
  · simp

/-- Restriction to an invariant open preserves the exact kernel relation. -/
theorem restrictProjection_isKernelPair (h : IsKernelPair q s t) (W : X.Opens)
    (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) :
    IsKernelPair (restrictProjection q h W hW) (s ∣_ W)
      ((R.isoOfEq hW).hom ≫ t ∣_ W) := by
  refine IsPullback.of_bot ?_ ?_ (restrictProjection_isPullback q h W hW)
  · simpa [Category.assoc] using (isPullback_morphismRestrict s W).paste_vert h
  · simp [← cancel_mono (descend q h W hW).ι, Category.assoc, h.w]

instance restrictProjection_surjective (h : IsKernelPair q s t) (W : X.Opens)
    (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) : Surjective (restrictProjection q h W hW) := by
  constructor
  intro y
  obtain ⟨x, hx⟩ := q.surjective ((descend q h W hW).ι y)
  obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
    (restrictProjection_isPullback q h W hW) y x hx.symm
  exact ⟨w, hw⟩

/-- Finite locally free surjective quotient maps keep these properties on
invariant open restrictions. -/
theorem restrictProjection_properties [IsFinite q] [LocallyOfFinitePresentation q]
    (h : IsKernelPair q s t) (W : X.Opens) (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) :
    IsFinite (restrictProjection q h W hW) ∧ Flat (restrictProjection q h W hW) ∧
      LocallyOfFinitePresentation (restrictProjection q h W hW) ∧
      Surjective (restrictProjection q h W hW) := by
  refine ⟨?_, inferInstance, ?_, inferInstance⟩ <;> unfold restrictProjection <;> infer_instance

/-- The quotient universal property holds on every invariant open overlap. -/
theorem restrictProjection_universal_property (h : IsKernelPair q s t) (W : X.Opens)
    (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) (T : Scheme.{u}) (f : W.toScheme ⟶ T)
    (hf : (s ∣_ W) ≫ f = ((R.isoOfEq hW).hom ≫ t ∣_ W) ≫ f) :
    ∃! g : (descend q h W hW).toScheme ⟶ T, restrictProjection q h W hW ≫ g = f :=
  Quotient.Construction.QuotientDescent.existsUnique_desc (restrictProjection q h W hW)
    (restrictProjection_isKernelPair q h W hW) f hf

/-- Any effective quotient of the relation on an invariant open is canonically
an open subscheme of the larger quotient. The quotient square is cartesian. -/
theorem existsUnique_open_transition (h : IsKernelPair q s t) (W : X.Opens)
    (hW : s ⁻¹ᵁ W = t ⁻¹ᵁ W) {Q' : Scheme.{u}}
    (q' : W.toScheme ⟶ Q') [EffectiveEpi q']
    (h' : IsKernelPair q' (s ∣_ W) ((R.isoOfEq hW).hom ≫ t ∣_ W)) :
    ∃! f : Q' ⟶ Q,
      q' ≫ f = W.ι ≫ q ∧ IsOpenImmersion f ∧ IsPullback q' W.ι f q := by
  obtain ⟨e, he, _⟩ := Quotient.Construction.QuotientDescent.existsUnique_iso q' (restrictProjection q h W hW)
    h' (restrictProjection_isKernelPair q h W hW)
  let f := e.hom ≫ (descend q h W hW).ι
  have hf : q' ≫ f = W.ι ≫ q := by
    rw [show f = e.hom ≫ (descend q h W hW).ι from rfl,
      ← Category.assoc, he, restrictProjection_ι]
  have hpb : IsPullback q' W.ι f q := by
    refine (restrictProjection_isPullback q h W hW).of_iso
      (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ (by simp) ?_ (by simp)
    · simp [← he]
    · simp [f]
  refine ⟨f, ⟨hf, inferInstance, hpb⟩, ?_⟩
  intro f' hf'
  exact (cancel_epi q').mp (hf'.1.trans hf.symm)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantOpensEq.Construction.InvariantOpens

import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ClosedAmbientNaturality
import Mathlib.CategoryTheory.Subfunctor.Image

/-! # Closed Ambient Range -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ClosedAmbientRange

noncomputable section

/-! The image of the closed-ambient Hilbert map consists precisely of
families whose defining ideal contains the ambient embedding's kernel. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X Y : Over S} (j : X ⟶ Y) [IsClosedImmersion j.left]
variable {T : Over S} (F : Functor.Family Y T) (hF : (ClosedAmbientMap.ambientEmbedding j T).ker ≤ F.val)

def closedAmbientLift : F.val.subscheme ⟶ Functor.ambient X T :=
  IsClosedImmersion.lift (ClosedAmbientMap.ambientEmbedding j T) F.val.subschemeι
    (by simpa only [F.val.ker_subschemeι] using hF)

theorem closedAmbientLift_fac : closedAmbientLift j F hF ≫ ClosedAmbientMap.ambientEmbedding j T = F.val.subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

instance closedAmbientLift_isClosedImmersion : IsClosedImmersion (closedAmbientLift j F hF) := by
  let : IsClosedImmersion (closedAmbientLift j F hF ≫ ClosedAmbientMap.ambientEmbedding j T) :=
    (closedAmbientLift_fac j F hF).symm ▸ inferInstanceAs (IsClosedImmersion F.val.subschemeι)
  exact IsClosedImmersion.of_comp_isClosedImmersion (closedAmbientLift j F hF) (ClosedAmbientMap.ambientEmbedding j T)

theorem closedAmbientLift_projection :
    closedAmbientLift j F hF ≫ Functor.ambientProjection X T = Functor.familyProjection Y F.val := by
  rw [← ClosedAmbientMap.ambientEmbedding_projection j T, ← Category.assoc, closedAmbientLift_fac]
  rfl

def restrictAmbientFamily : Functor.Family X T := by
  let l := closedAmbientLift j F hF
  have he : l ≫ Functor.ambientProjection X T = Functor.familyProjection Y F.val := closedAmbientLift_projection j F hF
  let : Flat (l ≫ Functor.ambientProjection X T) := he.symm ▸ F.property.1
  let : IsProper (l ≫ Functor.ambientProjection X T) := he.symm ▸ F.property.2.1
  let : LocallyOfFinitePresentation (l ≫ Functor.ambientProjection X T) := he.symm ▸ F.property.2.2
  exact Closed.ImmersionFamily.Hilbert.closedImmersionFamily X l

theorem pushforward_restrictAmbientFamily :
    ClosedAmbientMap.pushforwardFamily j (restrictAmbientFamily j F hF) = F := by
  apply Subtype.ext
  change (closedAmbientLift j F hF).ker.map (ClosedAmbientMap.ambientEmbedding j T) = F.val
  rw [Scheme.IdealSheafData.map_ker, closedAmbientLift_fac, F.val.ker_subschemeι]

theorem restrictAmbientFamily_ideal :
    (restrictAmbientFamily j F hF).val = F.val.comap (ClosedAmbientMap.ambientEmbedding j T) := by
  have h := congrArg (fun G : Functor.Family Y T => G.val.comap (ClosedAmbientMap.ambientEmbedding j T))
    (pushforward_restrictAmbientFamily j F hF)
  exact (Closed.ImmersionIdealEmbedding.ideal_comap_map_closed (ClosedAmbientMap.ambientEmbedding j T) (restrictAmbientFamily j F hF).val).symm.trans h

omit hF in
theorem pushforwardFamily_range_iff :
    (∃ G : Functor.Family X T, ClosedAmbientMap.pushforwardFamily j G = F) ↔ (ClosedAmbientMap.ambientEmbedding j T).ker ≤ F.val := by
  constructor
  · rintro ⟨G, rfl⟩
    exact Scheme.Hom.le_ker_comp G.val.subschemeι (ClosedAmbientMap.ambientEmbedding j T)
  · intro h
    exact ⟨restrictAmbientFamily j F h, pushforward_restrictAmbientFamily j F h⟩

def closedAmbientHilbertLocus : Subfunctor (Functor.familyFunctor Y) :=
  Subfunctor.range (ClosedAmbientNaturality.closedAmbientTransformation j)

omit hF in
theorem closedAmbientHilbertLocus_mem :
    F ∈ (closedAmbientHilbertLocus j).obj (.op T) ↔ (ClosedAmbientMap.ambientEmbedding j T).ker ≤ F.val :=
  pushforwardFamily_range_iff j F

def closedAmbientHilbertEquivalence : Functor.familyFunctor X ≅ (closedAmbientHilbertLocus j).toFunctor := by
  let t : Functor.familyFunctor X ⟶ Functor.familyFunctor Y := ClosedAmbientNaturality.closedAmbientTransformation j
  let : Mono t := ClosedAmbientNaturality.closedAmbientTransformation_mono j
  let e := asIso (Subfunctor.toRange t)
  exact e

theorem closedAmbientHilbertEquivalence_inclusion :
    (closedAmbientHilbertEquivalence j).hom ≫ (closedAmbientHilbertLocus j).ι =
      ClosedAmbientNaturality.closedAmbientTransformation j := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ClosedAmbientRange

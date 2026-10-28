import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # Functor -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Functor

noncomputable section

/-!
The relative Hilbert functor before decomposition by Hilbert polynomial.
Families are actual ideal sheaves in a scheme-theoretic fiber product, with
flat, proper, locally finitely presented structure map. No parameter space
or representability assertion is included in this definition.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (X : Over S)

abbrev ambient (T : Over S) : Scheme.{u} := (T ⨯ X).left

def ambientMap {T U : Over S} (f : T ⟶ U) : ambient X T ⟶ ambient X U :=
  (prod.map f (𝟙 X)).left

def ambientProjection (T : Over S) : ambient X T ⟶ T.left :=
  (prod.fst : T ⨯ X ⟶ T).left

@[simp] theorem ambientMap_id (T : Over S) :
    ambientMap X (𝟙 T) = 𝟙 (ambient X T) := by
  change (prod.map (𝟙 T) (𝟙 X)).left = _
  rw [prod.map_id_id]
  rfl

theorem ambientMap_comp {T U V : Over S} (f : T ⟶ U) (g : U ⟶ V) :
    ambientMap X (f ≫ g) = ambientMap X f ≫ ambientMap X g := by
  change (prod.map (f ≫ g) (𝟙 X)).left = _
  rw [← Category.id_comp (𝟙 X), ← prod.map_map]
  rfl

theorem ambient_isPullback {T U : Over S} (f : T ⟶ U) :
    IsPullback (ambientProjection X T) (ambientMap X f)
      f.left (ambientProjection X U) :=
  (IsPullback.of_prod_fst_with_id f X).map (Over.forget S)

def familyProjection {T : Over S} (I : (ambient X T).IdealSheafData) :
    I.subscheme ⟶ T.left :=
  I.subschemeι ≫ ambientProjection X T

def IsFamily {T : Over S} (I : (ambient X T).IdealSheafData) : Prop :=
  Flat (familyProjection X I) ∧
  IsProper (familyProjection X I) ∧
  LocallyOfFinitePresentation (familyProjection X I)

def Family (T : Over S) := {I : (ambient X T).IdealSheafData // IsFamily X I}

/-- The map on closed subschemes induced by pullback of their ideal sheaves. -/
def familyMap {T U : Over S} (f : T ⟶ U)
    (I : (ambient X U).IdealSheafData) :
    (I.comap (ambientMap X f)).subscheme ⟶ I.subscheme :=
  (I.comapIso (ambientMap X f)).hom ≫
    pullback.snd (ambientMap X f) I.subschemeι

theorem family_ambient_isPullback {T U : Over S} (f : T ⟶ U)
    (I : (ambient X U).IdealSheafData) :
    IsPullback (I.comap (ambientMap X f)).subschemeι
      (familyMap X f I) (ambientMap X f) I.subschemeι := by
  apply isPullback_of_isClosedImmersion
  · dsimp [familyMap]
    rw [Category.assoc, ← pullback.condition,
      ← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  · simp only [Scheme.IdealSheafData.ker_subschemeι]

/-- Flatness, properness, and finite presentation are transported along an
actual cartesian square, not stipulated in the pullback construction. -/
theorem family_isPullback {T U : Over S} (f : T ⟶ U)
    (I : (ambient X U).IdealSheafData) :
    IsPullback (familyProjection X (I.comap (ambientMap X f)))
      (familyMap X f I) f.left (familyProjection X I) :=
  (family_ambient_isPullback X f I).paste_horiz (ambient_isPullback X f)

theorem isFamily_comap {T U : Over S} (f : T ⟶ U)
    (I : (ambient X U).IdealSheafData) (hI : IsFamily X I) :
    IsFamily X (I.comap (ambientMap X f)) := by
  exact ⟨MorphismProperty.of_isPullback (family_isPullback X f I).flip hI.1,
    MorphismProperty.of_isPullback (family_isPullback X f I).flip hI.2.1,
    MorphismProperty.of_isPullback (family_isPullback X f I).flip hI.2.2⟩

def pullbackFamily {T U : Over S} (f : T ⟶ U) (I : Family X U) : Family X T :=
  ⟨I.val.comap (ambientMap X f), isFamily_comap X f I.val I.property⟩

theorem pullbackFamily_id {T : Over S} (I : Family X T) :
    pullbackFamily X (𝟙 T) I = I := by
  apply Subtype.ext
  change I.val.comap (ambientMap X (𝟙 T)) = I.val
  rw [ambientMap_id, Scheme.IdealSheafData.comap_id]

theorem pullbackFamily_comp {T U V : Over S}
    (f : T ⟶ U) (g : U ⟶ V) (I : Family X V) :
    pullbackFamily X (f ≫ g) I =
      pullbackFamily X f (pullbackFamily X g I) := by
  apply Subtype.ext
  change I.val.comap (ambientMap X (f ≫ g)) =
    (I.val.comap (ambientMap X g)).comap (ambientMap X f)
  rw [ambientMap_comp, Scheme.IdealSheafData.comap_comp]

/-- The genuine relative Hilbert functor of proper flat finitely presented
closed subschemes of the fibers of X. -/
def familyFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Family X T.unop
  map f := ↾pullbackFamily X f.unop
  map_id T := by
    ext I
    exact pullbackFamily_id X I
  map_comp f g := by
    ext I
    exact pullbackFamily_comp X g.unop f.unop I

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Functor

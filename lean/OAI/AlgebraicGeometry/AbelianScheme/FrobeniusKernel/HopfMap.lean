import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteHopfPresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Hopf Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HopfMap.Construction

noncomputable section

/-! Recover native Hopf-coordinate maps from actual group-scheme maps.
Closed embeddings give coordinate surjections; flat covers give injections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {k : Type u} [Field k] {R B : CommHopfAlgCat k}
  (f : (hopfSpec (.of k)).obj (.op R) ⟶ (hopfSpec (.of k)).obj (.op B))

def nativeHopfCoordinateMap : B ⟶ R :=
  ((hopfSpec.fullyFaithful (R := .of k)).preimage f).unop

theorem nativeHopfCoordinateMap_spec :
    (hopfSpec (.of k)).map (nativeHopfCoordinateMap f).op = f :=
  (hopfSpec.fullyFaithful (R := .of k)).map_preimage f

theorem nativeHopfCoordinateMap_spec_left :
    Spec.map (CommRingCat.ofHom (nativeHopfCoordinateMap f).hom.toAlgHom.toRingHom) =
      f.hom.hom.left :=
  congrArg (fun t => t.hom.hom.left) (nativeHopfCoordinateMap_spec f)

theorem nativeHopfCoordinateMap_surjective [IsClosedImmersion f.hom.hom.left] :
    Function.Surjective (nativeHopfCoordinateMap f).hom := by
  have hf : IsClosedImmersion f.hom.hom.left := inferInstance
  let a := CommRingCat.ofHom (nativeHopfCoordinateMap f).hom.toAlgHom.toRingHom
  have : IsClosedImmersion (Spec.map a) :=
    (congrArg IsClosedImmersion (nativeHopfCoordinateMap_spec_left f)).mpr hf
  have hs := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).surjective.comp
    ((IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map a)).2.comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of B)).inv).surjective)
  change Function.Surjective
    ((Scheme.ΓSpecIso (.of B)).inv ≫ (Spec.map a).appTop ≫ (Scheme.ΓSpecIso (.of R)).hom) at hs
  simpa [a] using hs

theorem nativeHopfCoordinateMap_injective [Flat f.hom.hom.left] [Surjective f.hom.hom.left] :
    Function.Injective (nativeHopfCoordinateMap f).hom := by
  have hf : Flat f.hom.hom.left := inferInstance
  have hs : Surjective f.hom.hom.left := inferInstance
  let a := CommRingCat.ofHom (nativeHopfCoordinateMap f).hom.toAlgHom.toRingHom
  have : Flat (Spec.map a) := (congrArg Flat (nativeHopfCoordinateMap_spec_left f)).mpr hf
  have : Surjective (Spec.map a) := (congrArg Surjective (nativeHopfCoordinateMap_spec_left f)).mpr hs
  exact ((flat_and_surjective_SpecMap_iff a).mp ⟨inferInstance, inferInstance⟩).injective

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HopfMap.Construction

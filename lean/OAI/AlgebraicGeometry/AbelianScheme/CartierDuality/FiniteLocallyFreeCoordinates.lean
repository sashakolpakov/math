import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Finite Locally Free Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FiniteLocallyFreeCoordinates.Construction

noncomputable section

/-!
# CartierDuality: finite locally free group schemes and finite projective coordinates
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

/-- The affine finite locally free condition is exactly finite projectivity
of the coordinate module, over an arbitrary commutative base ring. -/
theorem finiteLocallyFree_spec_iff
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    (IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A))) ∧
      Flat (Spec.map (CommRingCat.ofHom (algebraMap R A))) ∧
      LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R A)))) ↔
        Module.Finite R A ∧ Module.Projective R A := by
  rw [IsFinite.SpecMap_iff, Flat.SpecMap_iff,
    LocallyOfFinitePresentation.SpecMap_iff]
  constructor
  · rintro ⟨hf, hflat, hfp⟩
    let : Module.Finite R A := RingHom.finite_algebraMap.mp hf
    let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hflat
    let : Algebra.FinitePresentation R A := RingHom.finitePresentation_algebraMap.mp hfp
    let : Module.FinitePresentation R A :=
      Module.FinitePresentation.of_finite_of_finitePresentation R A
    exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩
  · rintro ⟨hf, hp⟩
    let := hf
    let := hp
    let : Module.FinitePresentation R A := Module.finitePresentation_of_projective R A
    exact ⟨RingHom.finite_algebraMap.mpr inferInstance,
      RingHom.flat_algebraMap_iff.mpr inferInstance,
      RingHom.finitePresentation_algebraMap.mpr inferInstance⟩

/-- Every finite locally free group scheme over an affine base has a
finite projective coordinate Hopf algebra. This extracts the algebraic
input from scheme-theoretic hypotheses rather than assuming a presentation. -/
theorem exists_finiteProjective_hopfPresentation
    (R : CommRingCat.{u}) (G : Grp (Over (Spec R)))
    [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] :
    ∃ A : CommHopfAlgCat R,
      Module.Finite R A ∧ Module.Projective R A ∧
        Nonempty ((hopfSpec R).obj (Opposite.op A) ≅ G) := by
  have hAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨A, ⟨e⟩⟩ := (essImage_hopfSpec (R := R) (G := G)).mpr hAffine
  let i : ((hopfSpec R).obj A).X ≅ G.X := (Grp.forget _).mapIso e
  have : IsIso i.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec R)).map i.hom))
  have hlocal :
      IsFinite ((hopfSpec R).obj A).X.hom ∧
      Flat ((hopfSpec R).obj A).X.hom ∧
      LocallyOfFinitePresentation ((hopfSpec R).obj A).X.hom := by
    have hw : i.hom.left ≫ G.X.hom = ((hopfSpec R).obj A).X.hom := i.hom.w
    rw [← hw]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hp := (finiteLocallyFree_spec_iff R A.unop).mp hlocal
  exact ⟨A.unop, hp.1, hp.2, ⟨e⟩⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FiniteLocallyFreeCoordinates.Construction

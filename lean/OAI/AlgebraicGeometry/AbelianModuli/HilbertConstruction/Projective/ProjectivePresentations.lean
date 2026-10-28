import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.FiniteType

/-! # Projective Presentations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations

noncomputable section

/-!
Projective geometry needed by HilbertConstruction. Projective space is constructed from the
standard polynomial grading and base change to an arbitrary scheme. The
presentation structures below contain actual scheme morphisms and immersion
properties; they contain no moduli representability assumptions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R]

abbrev coordinateRing (n : ℕ) := MvPolynomial (Fin (n + 1)) R

abbrev coordinateGrading (n : ℕ) : ℕ → Submodule R (coordinateRing R n) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

instance coordinateGradedAlgebra (n : ℕ) : GradedAlgebra (coordinateGrading R n) :=
  MvPolynomial.gradedAlgebra

/-- The degree-zero part of the standard polynomial grading is its base ring. -/
def degreeZeroConstants (n : ℕ) : R ≃+* coordinateGrading R n 0 where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (Fin (n + 1)) r⟩
  invFun p := AddMonoidAlgebra.coeff (p.val) (0)
  left_inv r := MvPolynomial.coeff_zero_C r
  right_inv p := by
    apply Subtype.ext
    have hp : MvPolynomial.IsHomogeneous p.val 0 := p.property
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (n + 1))).mpr hp)).symm
  map_mul' r s := Subtype.ext (map_mul MvPolynomial.C r s)
  map_add' r s := Subtype.ext (map_add MvPolynomial.C r s)

instance coordinateRing_finiteType_over_zero (n : ℕ) :
    Algebra.FiniteType (coordinateGrading R n 0) (coordinateRing R n) := by
  let : IsScalarTower R (coordinateGrading R n 0) (coordinateRing R n) :=
    IsScalarTower.of_algebraMap_eq
      (R := R) (S := coordinateGrading R n 0) (A := coordinateRing R n)
      (fun _ => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    R (coordinateGrading R n 0) (coordinateRing R n)

/-- Projective space over an affine base, with its structure morphism. -/
def affineProjectiveSpace (n : ℕ) : Over (Spec (.of R)) :=
  Over.mk (Proj.toSpecZero (coordinateGrading R n) ≫
    Spec.map (CommRingCat.ofHom (degreeZeroConstants R n).toRingHom))

instance affineProjectiveSpace_proper (n : ℕ) :
    IsProper (affineProjectiveSpace R n).hom := by
  have : IsIso (CommRingCat.ofHom (degreeZeroConstants R n).toRingHom) :=
    (degreeZeroConstants R n).toCommRingCatIso.isIso_hom
  have : IsProper (Proj.toSpecZero (coordinateGrading R n)) := inferInstance
  have : IsProper (Spec.map (CommRingCat.ofHom (degreeZeroConstants R n).toRingHom)) :=
    inferInstance
  change IsProper (Proj.toSpecZero (coordinateGrading R n) ≫
    Spec.map (CommRingCat.ofHom (degreeZeroConstants R n).toRingHom))
  infer_instance

/-- Projective space over any base scheme, formed by base change from its
ring of global sections. -/
def projectiveSpaceOver (S : Scheme.{u}) (n : ℕ) : Over S :=
  (Over.pullback S.toSpecΓ).obj (affineProjectiveSpace Γ(S, ⊤) n)

instance projectiveSpaceOver_proper (S : Scheme.{u}) (n : ℕ) :
    IsProper (projectiveSpaceOver S n).hom := by
  dsimp [projectiveSpaceOver]
  infer_instance

/-- A projective presentation consists of a closed immersion into projective
space over the same base. -/
structure ProjectivePresentation {S : Scheme.{u}} (X : Over S) where
  dimension : ℕ
  embedding : X ⟶ projectiveSpaceOver S dimension
  closedImmersion : IsClosedImmersion embedding.left

attribute [instance] ProjectivePresentation.closedImmersion

theorem ProjectivePresentation.proper {S : Scheme.{u}} {X : Over S}
    (P : ProjectivePresentation X) : IsProper X.hom := by
  rw [← P.embedding.w]
  infer_instance

/-- A finite-type scheme with an open immersion into a scheme supplied
with a projective presentation over the same base. -/
structure QuasiProjectivePresentation {S : Scheme.{u}} (X : Over S) where
  locallyFiniteType : LocallyOfFiniteType X.hom
  quasiCompact : QuasiCompact X.hom
  compactification : Over S
  projective : ProjectivePresentation compactification
  embedding : X ⟶ compactification
  openImmersion : IsOpenImmersion embedding.left

attribute [instance] QuasiProjectivePresentation.openImmersion

theorem QuasiProjectivePresentation.separated {S : Scheme.{u}} {X : Over S}
    (P : QuasiProjectivePresentation X) : IsSeparated X.hom := by
  have := P.projective.proper
  rw [← P.embedding.w]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations

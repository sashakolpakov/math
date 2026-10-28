import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.Sections
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.GrassmannianProjectivity
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.GrassmannianRepresentation

/-! # Parameter Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ParameterScheme

noncomputable section

/-!
The global projective Grassmannian parameter scheme used by HilbertConstruction. This reuses the
constructive chart, gluing, Plücker, and quotient-classification support from Presentations;
it does not import or assume the Presentations Hilbert representability statement.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.GrassmannianRepresentation.Grassmannian

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]

/-- The actual scheme parametrizing rank-`card ι` quotients of the coordinate module on `ν`. -/
def grassmannParameterScheme (S : Scheme.{u}) : Over S :=
  HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := ν) S

/-- Its finite Plücker coordinate projective space over the base. -/
def grassmannParameterProjectiveSpace (S : Scheme.{u}) : Over S :=
  Over.mk (HilbertScheme.Presentations.Relative.GrassmannianProjectivity.PolynomialProjective.relativeProjectiveSpaceProjection (ι → ν) S)

/-- The actual closed Plücker embedding, as a morphism over the base. -/
def grassmannParameterEmbedding (S : Scheme.{u}) :
    grassmannParameterScheme (ι := ι) (ν := ν) S ⟶ grassmannParameterProjectiveSpace (ι := ι) (ν := ν) S :=
  Over.homMk (HilbertScheme.Presentations.Relative.GrassmannianProjectivity.Grassmannian.relativeGrassmannianPluckerEmbedding S) (HilbertScheme.Presentations.Relative.GrassmannianProjectivity.Grassmannian.relativeGrassmannianPluckerEmbedding_over S)

instance grassmannParameterEmbedding_isClosedImmersion (S : Scheme.{u}) :
    IsClosedImmersion (grassmannParameterEmbedding (ι := ι) (ν := ν) S).left :=
  HilbertScheme.Presentations.Relative.GrassmannianProjectivity.Grassmannian.relativeGrassmannianPluckerEmbedding_isClosedImmersion S

/-- For finitely many ambient coordinates, the Grassmannian is proper over its base. -/
instance grassmannParameterScheme_proper (S : Scheme.{u}) [Finite ν] :
    IsProper (grassmannParameterScheme (ι := ι) (ν := ν) S).hom :=
  HilbertScheme.Presentations.Grassmannian.BaseChange.grassmannianStructureMap_proper S

/-- The parameter scheme commutes with arbitrary base change. -/
theorem grassmannParameterScheme_baseChange {S T : Scheme.{u}} (f : T ⟶ S) :
    IsPullback (HilbertScheme.Presentations.Grassmannian.BaseMap.grassmannianBaseMap (ι := ι) (ν := ν) f)
      (grassmannParameterScheme (ι := ι) (ν := ν) T).hom
      (grassmannParameterScheme (ι := ι) (ν := ν) S).hom f :=
  HilbertScheme.Presentations.Grassmannian.BaseChange.grassmannianBaseMap_isPullback f

variable [Fintype ν] [DecidableEq ν] {S : Scheme.{u}} (A : CommRingCat.{u}) (f : Spec A ⟶ S)

/-- Every affine test over any base is classified by its actual finite-projective quotient. -/
def grassmannParameterAffinePointEquiv :
    Module.Grassmannian A (ν → A) (Fintype.card ι) ≃
      (Over.mk f ⟶ grassmannParameterScheme (ι := ι) (ν := ν) S) :=
  (HilbertScheme.Presentations.Affine.GrassmannianRepresentation.Grassmannian.affineGrassmannianPointEquiv (ι := ι) (ν := ν) A).trans
    (Cartesian.Sections.cartesianSectionHomEquiv (grassmannParameterScheme_baseChange (ι := ι) (ν := ν) f))

/-- A prescribed quotient determines a unique morphism to the global parameter scheme. -/
theorem grassmannParameter_existsUnique_classifyingMap
    (N : Module.Grassmannian A (ν → A) (Fintype.card ι)) :
    ∃! g : Over.mk f ⟶ grassmannParameterScheme (ι := ι) (ν := ν) S,
      (grassmannParameterAffinePointEquiv (ι := ι) (ν := ν) A f).symm g = N := by
  let e := grassmannParameterAffinePointEquiv (ι := ι) (ν := ν) A f
  refine ⟨e N, e.symm_apply_apply N, ?_⟩
  intro g hg
  exact e.symm.injective (hg.trans (e.symm_apply_apply N).symm)

/-- The classifying morphism is the quotient map over its coefficient ring followed by base change. -/
theorem grassmannParameterAffinePointEquiv_left
    (N : Module.Grassmannian A (ν → A) (Fintype.card ι)) :
    (grassmannParameterAffinePointEquiv (ι := ι) (ν := ν) A f N).left =
      HilbertScheme.Presentations.Affine.QuotientClassifyingMap.Grassmannian.quotientClassifyingMap A N ≫ HilbertScheme.Presentations.Grassmannian.BaseMap.grassmannianBaseMap f := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ParameterScheme

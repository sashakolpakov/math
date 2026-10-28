import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth Projective -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective

noncomputable section

/-!
# Actual smooth projective presentations over the complex numbers

A projective presentation is a closed immersion into the `Proj` scheme of a
standard graded complex polynomial ring, commuting with the structure maps to
`Spec ℂ`. Smoothness is mathlib's smoothness of the structure morphism.

These are raw presentations: connectedness and irreducibility are not imposed.
There is no cohomology, cycle map, analytic topology, or unproved comparison
property in either structure.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- A genuine projective presentation of an actual complex scheme morphism. -/
structure ProjectivePresentation (X : Scheme) (f : X ⟶ ProjectiveSpace.complexBase) where
  /-- Dimension of the ambient standard projective space. -/
  ambientDimension : ℕ
  /-- The actual scheme morphism giving the projective embedding. -/
  embedding : X ⟶ ProjectiveSpace.projectiveSpace ambientDimension
  /-- Closed immersion has its existing scheme-theoretic meaning in mathlib. -/
  closedImmersion : IsClosedImmersion embedding
  /-- The embedding is a morphism over `Spec ℂ`. -/
  over_base : embedding ≫ ProjectiveSpace.projectiveSpaceToBase ambientDimension = f

namespace ProjectivePresentation

variable {X : Scheme} {f : X ⟶ ProjectiveSpace.complexBase}

instance (P : ProjectivePresentation X f) : IsClosedImmersion P.embedding :=
  P.closedImmersion

/-- The displayed structure map is the composite through the projective space. -/
theorem structureMap_eq (P : ProjectivePresentation X f) :
    f = P.embedding ≫ ProjectiveSpace.projectiveSpaceToBase P.ambientDimension :=
  P.over_base.symm

/-- Forgetting a projective presentation gives a morphism in the category over `Spec ℂ`. -/
def toOverHom (P : ProjectivePresentation X f) :
    Over.mk f ⟶ Over.mk (ProjectiveSpace.projectiveSpaceToBase P.ambientDimension) :=
  Over.homMk P.embedding P.over_base

@[simp]
theorem toOverHom_left (P : ProjectivePresentation X f) :
    P.toOverHom.left = P.embedding := rfl

/-- Packaging does not add any hypothesis beyond an actual closed projective embedding. -/
theorem nonempty_iff :
    Nonempty (ProjectivePresentation X f) ↔
      ∃ (n : ℕ) (i : X ⟶ ProjectiveSpace.projectiveSpace n),
        IsClosedImmersion i ∧ i ≫ ProjectiveSpace.projectiveSpaceToBase n = f := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.ambientDimension, P.embedding, P.closedImmersion, P.over_base⟩
  · rintro ⟨n, i, hi, hf⟩
    exact ⟨⟨n, i, hi, hf⟩⟩

/-- The underlying point map of the projective embedding is a closed embedding. -/
theorem isClosedEmbedding (P : ProjectivePresentation X f) :
    Topology.IsClosedEmbedding P.embedding :=
  P.embedding.isClosedEmbedding

/-- In particular, the embedding is injective on underlying scheme points. -/
theorem embedding_injective (P : ProjectivePresentation X f) :
    Function.Injective P.embedding :=
  P.isClosedEmbedding.injective

end ProjectivePresentation

/-- A smooth projective complex scheme with a chosen projective presentation.

The carrier is an actual scheme; the projectivity and smoothness fields use
only genuine algebraic-geometric definitions. No assertion about the analytic
space or Hodge theory is built into the data. -/
structure SmoothProjectivePresentation where
  carrier : Scheme
  structureMap : carrier ⟶ ProjectiveSpace.complexBase
  projective : ProjectivePresentation carrier structureMap
  smooth : Smooth structureMap

namespace SmoothProjectivePresentation

variable (P : SmoothProjectivePresentation)

/-- The ambient dimension of the chosen projective embedding. -/
abbrev ambientDimension : ℕ := P.projective.ambientDimension

/-- The chosen projective embedding. -/
abbrev embedding : P.carrier ⟶ ProjectiveSpace.projectiveSpace P.ambientDimension :=
  P.projective.embedding

instance : Smooth P.structureMap := P.smooth

instance : IsClosedImmersion P.embedding := P.projective.closedImmersion

/-- The carrier together with its specified complex structure map. -/
def toOver : Over ProjectiveSpace.complexBase := Over.mk P.structureMap

@[simp]
theorem toOver_left : P.toOver.left = P.carrier := rfl

@[simp]
theorem toOver_hom : P.toOver.hom = P.structureMap := rfl

@[reassoc]
theorem embedding_over :
    P.embedding ≫ ProjectiveSpace.projectiveSpaceToBase P.ambientDimension = P.structureMap :=
  P.projective.over_base

/-- Local finite presentation follows from genuine smoothness; it is not assumed. -/
instance : LocallyOfFinitePresentation P.structureMap := inferInstance

/-- Flatness follows from genuine smoothness; it is not assumed. -/
instance : Flat P.structureMap := inferInstance

/-- The actual structure morphism has standard smooth affine neighborhoods. -/
theorem exists_standardSmooth_neighborhood (x : P.carrier) :
    ∃ (U : ProjectiveSpace.complexBase.Opens) (_ : IsAffineOpen U)
      (V : P.carrier.Opens) (_ : IsAffineOpen V) (_ : x ∈ V)
      (e : V ≤ P.structureMap ⁻¹ᵁ U),
      (P.structureMap.appLE U V e).hom.IsStandardSmooth :=
  Smooth.exists_isStandardSmooth P.structureMap x

end SmoothProjectivePresentation

end

end OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective

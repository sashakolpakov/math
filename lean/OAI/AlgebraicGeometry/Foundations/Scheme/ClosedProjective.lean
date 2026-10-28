import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpaceFiniteType
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective

/-! # Closed Projective -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme

/-!
# Algebraic consequences of a closed immersion into a projective spectrum

These lemmas concern actual schemes, morphisms, and the `Proj` construction in
mathlib. They supply properness, finite type, and Noetherian consequences used
by a projective presentation. Compactness here refers to the scheme's Zariski
topology; no assertion about an analytification is made in this module.
-/

set_option autoImplicit false
set_option warningAsError true

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

section General

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Proper morphisms are quasi-compact and locally of finite type, the two
conditions defining a morphism of finite type. -/
theorem ClosedProjective.finiteType_of_isProper [IsProper f] :
    LocallyOfFiniteType f ∧ QuasiCompact f :=
  ⟨inferInstance, inferInstance⟩

/-- A proper scheme over a Noetherian affine scheme is Noetherian. -/
theorem ClosedProjective.isNoetherian_of_isProper_toSpec {R : Type u} [CommRing R]
    [IsNoetherianRing R] (g : X ⟶ Spec (.of R)) [IsProper g] :
    AlgebraicGeometry.IsNoetherian X := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  let : CompactSpace X := (quasiCompact_iff_compactSpace g).mp inferInstance
  exact ⟨⟩

end General

section ProjectiveSpectrum

variable {σ A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A]
variable {X : Scheme.{u}} (i : X ⟶ Proj 𝒜) [IsClosedImmersion i]

/-- A closed subscheme of a finite-type projective spectrum is proper over its
actual degree-zero ring. -/
theorem ClosedProjective.closedImmersion_proj_isProper :
    IsProper (i ≫ Proj.toSpecZero 𝒜) := by
  infer_instance

/-- The morphism in `closedImmersion_proj_isProper` is of finite type. -/
theorem ClosedProjective.closedImmersion_proj_finiteType :
    LocallyOfFiniteType (i ≫ Proj.toSpecZero 𝒜) ∧
      QuasiCompact (i ≫ Proj.toSpecZero 𝒜) :=
  ClosedProjective.finiteType_of_isProper _

include 𝒜 i in
/-- Algebraic (Zariski) compactness of a closed subscheme of `Proj`. -/
theorem ClosedProjective.closedImmersion_proj_compactSpace : CompactSpace X :=
  (quasiCompact_iff_compactSpace (i ≫ Proj.toSpecZero 𝒜)).mp inferInstance

include 𝒜 i in
/-- A closed subscheme of a finite-type `Proj` is Noetherian when the
actual degree-zero coefficient ring is Noetherian. -/
theorem ClosedProjective.closedImmersion_proj_isNoetherian [IsNoetherianRing (𝒜 0)] :
    AlgebraicGeometry.IsNoetherian X :=
  ClosedProjective.isNoetherian_of_isProper_toSpec (i ≫ Proj.toSpecZero 𝒜)

/-- Properness survives an arbitrary scheme-theoretic base change. -/
theorem ClosedProjective.closedImmersion_proj_baseChange_isProper {T : Scheme.{u}}
    (g : T ⟶ Spec (.of (𝒜 0))) :
    IsProper (Limits.pullback.snd (i ≫ Proj.toSpecZero 𝒜) g) := by
  infer_instance

/-- Finite type survives the same scheme-theoretic base change. -/
theorem ClosedProjective.closedImmersion_proj_baseChange_finiteType {T : Scheme.{u}}
    (g : T ⟶ Spec (.of (𝒜 0))) :
    LocallyOfFiniteType (Limits.pullback.snd (i ≫ Proj.toSpecZero 𝒜) g) ∧
      QuasiCompact (Limits.pullback.snd (i ≫ Proj.toSpecZero 𝒜) g) :=
  ClosedProjective.finiteType_of_isProper _

/-- An actual surjective identification of base rings yields a proper
morphism to the target affine scheme, without adding properness as a premise. -/
theorem ClosedProjective.closedImmersion_proj_changeBase_isProper {R : Type u} [CommRing R]
    (φ : R →+* (𝒜 0)) (hφ : Function.Surjective φ) :
    IsProper (i ≫ Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom φ)) := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ) hφ
  infer_instance

end ProjectiveSpectrum

/-- The standard complex projective-space structure morphism is proper.
The degree-zero ring is related to the complex base by the proved constants
isomorphism, rather than an assumed comparison. -/
instance ClosedProjective.projectiveSpaceToBase_isProper (n : ℕ) :
    IsProper (ProjectiveSpace.projectiveSpaceToBase n) := by
  unfold ProjectiveSpace.projectiveSpaceToBase
  let : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (ProjectiveSpace.degreeZeroConstants n).toRingHom)) :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (ProjectiveSpace.degreeZeroConstants n).toRingHom)
      (ProjectiveSpace.degreeZeroConstants n).surjective
  infer_instance

/-- Finite type of the actual complex projective-space structure morphism. -/
theorem ClosedProjective.projectiveSpaceToBase_finiteType (n : ℕ) :
    LocallyOfFiniteType (ProjectiveSpace.projectiveSpaceToBase n) ∧
      QuasiCompact (ProjectiveSpace.projectiveSpaceToBase n) :=
  ClosedProjective.finiteType_of_isProper _

/-- Standard complex projective space is a Noetherian scheme. -/
instance ClosedProjective.projectiveSpace_isNoetherian (n : ℕ) :
    AlgebraicGeometry.IsNoetherian (ProjectiveSpace.projectiveSpace n) :=
  ClosedProjective.isNoetherian_of_isProper_toSpec (ProjectiveSpace.projectiveSpaceToBase n)

/-- A genuine closed projective embedding supplies properness over the complex
base; this property need not be added as a field of a presentation. -/
theorem ClosedProjective.closedImmersion_projectiveSpace_isProper {X : Scheme} (n : ℕ)
    (i : X ⟶ ProjectiveSpace.projectiveSpace n) [IsClosedImmersion i] :
    IsProper (i ≫ ProjectiveSpace.projectiveSpaceToBase n) := by
  infer_instance

section

variable {X : Scheme} {f : X ⟶ ProjectiveSpace.complexBase} (P : SmoothProjective.ProjectivePresentation X f)

include P

/-- Properness is a consequence of the actual chosen projective embedding. -/
theorem SmoothProjective.ProjectivePresentation.isProper : IsProper f := by
  rw [P.structureMap_eq]
  exact ClosedProjective.closedImmersion_projectiveSpace_isProper P.ambientDimension P.embedding

/-- Both conditions of finite type follow from the chosen projective embedding. -/
theorem SmoothProjective.ProjectivePresentation.finiteType : LocallyOfFiniteType f ∧ QuasiCompact f := by
  let : IsProper f := P.isProper
  exact ClosedProjective.finiteType_of_isProper f

/-- The carrier of an actual complex projective presentation is Noetherian. -/
theorem SmoothProjective.ProjectivePresentation.isNoetherian : AlgebraicGeometry.IsNoetherian X := by
  let : IsProper f := P.isProper
  exact ClosedProjective.isNoetherian_of_isProper_toSpec f

/-- Finite presentation locally on source and target follows because the base
is the spectrum of the Noetherian field of complex numbers. -/
theorem SmoothProjective.ProjectivePresentation.locallyOfFinitePresentation : LocallyOfFinitePresentation f := by
  let : IsProper f := P.isProper
  infer_instance

/-- The actual projective presentation remains proper after any base change. -/
theorem SmoothProjective.ProjectivePresentation.baseChange_isProper {T : Scheme} (g : T ⟶ ProjectiveSpace.complexBase) :
    IsProper (Limits.pullback.snd f g) := by
  let : IsProper f := P.isProper
  infer_instance

end

variable (P : SmoothProjective.SmoothProjectivePresentation)

/-- The properness instance is proved from projectivity, not stored in the
smooth-projective data. -/
instance SmoothProjective.SmoothProjectivePresentation.isProper : IsProper P.structureMap := P.projective.isProper

/-- The scheme underlying a smooth projective presentation is Noetherian. -/
instance SmoothProjective.SmoothProjectivePresentation.isNoetherian : AlgebraicGeometry.IsNoetherian P.carrier :=
  P.projective.isNoetherian

/-- The structure morphism of a smooth projective presentation is of finite type. -/
theorem SmoothProjective.SmoothProjectivePresentation.finiteType : LocallyOfFiniteType P.structureMap ∧ QuasiCompact P.structureMap :=
  ClosedProjective.finiteType_of_isProper _

end OAI.AlgebraicGeometry.Foundations.Scheme

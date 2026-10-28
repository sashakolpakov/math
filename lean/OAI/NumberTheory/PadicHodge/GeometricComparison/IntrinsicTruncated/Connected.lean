import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.Projectivity
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.Bounds
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormTraceData
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.QuotientInjective

/-! # Connected -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

section

/-! The normalized native top-form trace on the actual finite-level
abelian models, with projectivity and the identity section supplied
by the original geometry. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace IntrinsicTruncated.Connected.NativeTruncatedBase
variable (q : ℕ) [Fact q.Prime] (n : ℕ)

instance artinian : IsArtinianRing (TruncatedModel.NativeTruncatedBase.Ring q n) :=
  isArtinian_of_finite (R := TruncatedModel.NativeTruncatedBase.Ring q n) (M := TruncatedModel.NativeTruncatedBase.Ring q n)

instance selfInjective : Module.Injective (TruncatedModel.NativeTruncatedBase.Ring q n) (TruncatedModel.NativeTruncatedBase.Ring q n) :=
  IntegralComparison.Witt.QuotientInjective.injective q (ZMod q) n

end IntrinsicTruncated.Connected.NativeTruncatedBase

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

attribute [local instance] MvPolynomial.gradedAlgebra

def Geometry.AbelianH1Model.truncatedTraceDimension (n : ℕ) : ℕ :=
  Classical.choose (A.truncatedModel_projective_positive n)

def Geometry.AbelianH1Model.truncatedTraceEmbedding (n : ℕ) :
    (A.truncatedModel n).scheme.left ⟶
      IntegralComparison.Projectivity.Construction.projectiveSpace (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedTraceDimension n + 1) :=
  Classical.choose (Classical.choose_spec (A.truncatedModel_projective_positive n))

instance Geometry.AbelianH1Model.truncatedTraceEmbedding_closed (n : ℕ) : IsClosedImmersion (A.truncatedTraceEmbedding n) :=
  (Classical.choose_spec (Classical.choose_spec (A.truncatedModel_projective_positive n))).1

theorem Geometry.AbelianH1Model.truncatedTraceEmbedding_over (n : ℕ) :
    A.truncatedTraceEmbedding n ≫
      IntegralComparison.Projectivity.Construction.projectiveSpaceToSpec (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedTraceDimension n + 1) =
      (A.truncatedModel n).scheme.hom :=
  (Classical.choose_spec (Classical.choose_spec (A.truncatedModel_projective_positive n))).2

def Geometry.AbelianH1Model.truncatedTraceMorphism (n : ℕ) :
    (A.truncatedModel n).scheme ⟶
      IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.model (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedTraceDimension n + 1) :=
  Over.homMk (A.truncatedTraceEmbedding n) (A.truncatedTraceEmbedding_over n)

instance Geometry.AbelianH1Model.truncatedTraceMorphism_closed (n : ℕ) :
    IsClosedImmersion (A.truncatedTraceMorphism n).left :=
  A.truncatedTraceEmbedding_closed n

def Geometry.AbelianH1Model.truncatedIdentitySection (n : ℕ) :
    Spec (CommRingCat.of (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)) ⟶ (A.truncatedModel n).scheme.left :=
  (1 : Over.mk (𝟙 (Spec (CommRingCat.of (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)))) ⟶
    (A.truncatedModel n).scheme).left

theorem Geometry.AbelianH1Model.truncatedIdentitySection_over (n : ℕ) :
    A.truncatedIdentitySection n ≫ (A.truncatedModel n).scheme.hom = 𝟙 _ :=
  (1 : Over.mk (𝟙 (Spec (CommRingCat.of (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)))) ⟶
    (A.truncatedModel n).scheme).w

instance Geometry.AbelianH1Model.truncatedModel_nonempty (n : ℕ) : Nonempty (A.truncatedModel n).scheme.left :=
  Nonempty.map (A.truncatedIdentitySection n) inferInstance

def Geometry.AbelianH1Model.truncatedTraceCover (n : ℕ) (i : ULift (Fin (A.truncatedTraceDimension n + 2))) :
    (A.truncatedModel n).scheme.left.Opens :=
  IntegralComparison.Intrinsic.TopFormTrace.cover (A.truncatedModel n).scheme (A.truncatedTraceMorphism n) i

theorem Geometry.AbelianH1Model.truncatedTraceCover_affine (n : ℕ) (i : ULift (Fin (A.truncatedTraceDimension n + 2))) :
    IsAffineOpen (A.truncatedTraceCover n i) :=
  IntegralComparison.Intrinsic.TopFormTrace.cover_affine (A.truncatedModel n).scheme (A.truncatedTraceMorphism n) i

theorem Geometry.AbelianH1Model.truncatedTraceCover_top (n : ℕ) : (⨆ i, A.truncatedTraceCover n i) = ⊤ :=
  IntegralComparison.Intrinsic.TopFormTrace.cover_top (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)

abbrev Geometry.AbelianH1Model.TruncatedTopFormCohomology (n : ℕ) :=
  IntegralComparison.Intrinsic.TopFormTrace.cohomology (A.truncatedModel n).scheme
    (A.truncatedTraceMorphism n) A.dimension

def Geometry.AbelianH1Model.truncatedTopFormTraceData (n : ℕ) :
    {τ : A.TruncatedTopFormCohomology n →+
      IntegralComparison.Projective.TopTracePairing.coefficientRing (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) //
        Function.Bijective τ} :=
  IntegralComparison.Intrinsic.TopFormTraceData.data (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedTraceDimension n + 2) le_rfl A.dimension
    (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)

def Geometry.AbelianH1Model.truncatedTopFormTrace (n : ℕ) : A.TruncatedTopFormCohomology n →+
    IntegralComparison.Projective.TopTracePairing.coefficientRing (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) :=
  (A.truncatedTopFormTraceData n).val

theorem Geometry.AbelianH1Model.truncatedTopFormTrace_bijective (n : ℕ) :
    Function.Bijective (A.truncatedTopFormTrace n) :=
  (A.truncatedTopFormTraceData n).property

def Geometry.AbelianH1Model.truncatedTopFormTraceIso (n : ℕ) : A.TruncatedTopFormCohomology n ≃+
    IntegralComparison.Projective.TopTracePairing.coefficientRing (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) :=
  AddEquiv.ofBijective (A.truncatedTopFormTrace n) (A.truncatedTopFormTrace_bijective n)

theorem Geometry.AbelianH1Model.truncatedTopFormTraceIso_apply (n : ℕ) (x : A.TruncatedTopFormCohomology n) :
    A.truncatedTopFormTraceIso n x = A.truncatedTopFormTrace n x := rfl

theorem Geometry.AbelianH1Model.truncatedTopFormTrace_eq (n : ℕ) :
    A.truncatedTopFormTrace n =
      IntegralComparison.Intrinsic.TopFormTrace.trace (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
        (A.truncatedTraceDimension n + 2) le_rfl A.dimension :=
  IntegralComparison.Intrinsic.TopFormTraceData.map_eq (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedTraceDimension n + 2) le_rfl A.dimension
    (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)

end

/-! Connectedness of the actual finite-level target follows from
the surjective closed reduction of its original connected special fiber. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq) (n : ℕ)

instance Geometry.AbelianH1Model.truncatedModel_preconnected : PreconnectedSpace (A.truncatedModel n).scheme.left := by
  let : ConnectedSpace A.specialFiber.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.specialFiber.scheme.hom
  exact (A.truncatedReduction n).surjective.denseRange.preconnectedSpace
    (A.truncatedReduction n).continuous

end

end OAI.NumberTheory.PadicHodge.GeometricComparison

import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ComplexBlockBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.FiberProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter

/-! # Polarized Block Basis -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedBlockBasis.Construction

noncomputable section

/-!
Polarization positivity supplies the projective presentation used in the
complex period comparison. Thus a genuine PEL source has a rank-three
integral basis in every CMPoints block without a projectivity assumption.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

def polarizedProjectivePresentationTransport {S : Scheme} {X Y : Over S}
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation Y) (e : X ≅ Y) : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X where
  dimension := P.dimension
  embedding := e.hom ≫ P.embedding
  closedImmersion := by
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
    exact inferInstanceAs (IsClosedImmersion (e.hom.left ≫ P.embedding.left))

def polarizedPELComplexPresentation {R : Type} [CommRing R] {g N : ℕ}
    (F : TateComparison.PEL.PELFamilyData R g N Foundations.Scheme.ProjectiveSpace.complexBase) {δ : Fin g → ℕ} {c : R →+* R}
    (hF : F.IsPEL δ c) : Foundations.Scheme.SmoothProjective.ProjectivePresentation F.abelian.scheme.left F.abelian.scheme.hom :=
  AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation
    (polarizedProjectivePresentationTransport
      ((F.toPolarized hF).geometricFiber_projectivePresentation ℂ (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))
      F.abelian.pullbackIdIso.symm)

variable {E L : Type} [Field E] [NumberField E] [IsGalois ℚ E]
  [Field L] [NumberField L] {κ : L →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)
  (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
  {N : ℕ} (F : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N Foundations.Scheme.ProjectiveSpace.complexBase)
  {δ : Fin (3 * s) → ℕ} {c : NumberField.RingOfIntegers E →+* NumberField.RingOfIntegers E}
  (hF : F.IsPEL δ c)

def polarizedCMPointsBlockBasis (τ : Gal(E/ℚ)) :
    Module.Basis (Fin 3) ℤ_[q]
      (CM.PointsTateBlocks.Construction.l45IntegralTateBlock j iota hsplit (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) F τ) :=
  ComplexBlockBasis.Construction.complexCMPointsBlockBasis j iota hsplit s hs hdegree F (polarizedPELComplexPresentation F hF) τ

include hs hdegree hF in
theorem polarizedCMPointsBlock_finrank (τ : Gal(E/ℚ)) :
    Module.finrank ℤ_[q]
      (CM.PointsTateBlocks.Construction.l45IntegralTateBlock j iota hsplit (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) F τ) = 3 := by
  simpa only [Fintype.card_fin] using
    Module.finrank_eq_card_basis (polarizedCMPointsBlockBasis j iota hsplit s hs hdegree F hF τ)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedBlockBasis.Construction

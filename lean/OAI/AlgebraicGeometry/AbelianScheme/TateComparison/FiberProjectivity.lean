import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiberPolarizationType
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.FiberProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexBasis

/-! # Fiber Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The committed ample-embedding theorem supplies actual projective
presentations of the PEL fibers. Complex fibers therefore have their
proved integral and rational Tate ranks, with no projectivity input. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def FiberProjectivity.relativeProjectivePresentation_transport {S : Scheme.{0}} {X Y : Over S}
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation Y) (e : X ≅ Y) :
    AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X where
  dimension := P.dimension
  embedding := e.hom ≫ P.embedding
  closedImmersion := by
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
    exact inferInstanceAs (IsClosedImmersion (e.hom.left ≫ P.embedding.left))

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.HasIntegralModelGeometry)

/-- The actual fiber has a closed projective embedding, constructed from
its supplied polarization positivity and the proved ample-embedding theorem. -/
def Data.SphericalPELAlbaneseData.fiberProjectivePresentation {k : Type} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b) :
    AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (D.fiberFamily b x).abelian.scheme := by
  have : IsReduced (Over.mk (b ≫ D.generic)).left := inferInstanceAs (IsReduced (Spec (.of k)))
  let P := D.model.family.pullback (D.modelGeometricPoint b x).left
  have hp : P.IsPEL D.reference.polarizationType
      (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom :=
    (h.classifies.1 (Over.mk (b ≫ D.generic)) (D.modelGeometricPoint b x)).1
  let e : (D.fiberFamily b x).abelian.scheme ≅ (P.abelian.pullback (𝟙 (Spec (.of k)))).scheme :=
    (D.model.family.pullbackComp (pullback.fst D.model.space.hom D.generic) x.left).abelian ≪≫
      P.abelian.pullbackIdIso.symm
  exact FiberProjectivity.relativeProjectivePresentation_transport
    ((P.toPolarized hp).geometricFiber_projectivePresentation k (𝟙 (Spec (.of k)))) e

def Data.SphericalPELAlbaneseData.complexFiberProjectivePresentation (b : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K))
    (x : D.GeometricPoint b) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation (D.fiberFamily b x).abelian.scheme.left (D.fiberFamily b x).abelian.scheme.hom :=
  AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation
    (D.fiberProjectivePresentation h b x)

def Data.SphericalPELAlbaneseData.complexFiberTateBasis (b : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K)) (x : D.GeometricPoint b) :
    Module.Basis (Fin (2 * (3 * s))) ℤ_[q]
      (Add.schemeTateModule (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q) :=
  ComplexBasis.complexTateBasis (D.fiberFamily b x).abelian (D.complexFiberProjectivePresentation h b x) q

include h in
theorem Data.SphericalPELAlbaneseData.complexFiberTate_finrank (b : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K)) (x : D.GeometricPoint b) :
    Module.finrank ℤ_[q]
      (Add.schemeTateModule (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q) = 6 * s := by
  have hr := ComplexBasis.complexTate_finrank (D.fiberFamily b x).abelian
    (D.complexFiberProjectivePresentation h b x) q
  simpa only [← Nat.mul_assoc] using hr

include h in
theorem Data.SphericalPELAlbaneseData.complexFiberRationalTate_finrank (b : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K)) (x : D.GeometricPoint b) :
    Module.finrank ℚ_[q]
      (Rational.rationalTateModule (D.fiberFamily b x).abelian.scheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) q) = 6 * s := by
  have hr := ComplexBasis.complexRationalTate_finrank (D.fiberFamily b x).abelian
    (D.complexFiberProjectivePresentation h b x) q
  simpa only [← Nat.mul_assoc] using hr

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison

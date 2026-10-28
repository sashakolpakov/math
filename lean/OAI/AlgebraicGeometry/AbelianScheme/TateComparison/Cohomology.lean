import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotient
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Branches

/-! # Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The statement-facing cohomology and differential maps use actual
complex base change and geometric pullback. Rational pullback is expressed
by clearing an integer denominator, without assuming an additive H1 API. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)

abbrev Data.SphericalPELAlbaneseData.complexGenericPoint : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom D.complexEmbedding)

abbrev Data.SphericalPELAlbaneseData.complexSpace := (Over.pullback D.complexGenericPoint).obj D.space
abbrev Data.SphericalPELAlbaneseData.complexAlbanese : CommGrp (Over Foundations.Scheme.ProjectiveSpace.complexBase) :=
  BaseChange.baseChangedGroup D.albaneseGroup.X D.complexGenericPoint

abbrev Data.SphericalPELAlbaneseData.complexAlbaneseMap (h : D.HasIntegralModelGeometry) :=
  (Over.pullback D.complexGenericPoint).map (D.albaneseMap h)

abbrev Data.SphericalPELAlbaneseData.H1 := PELModuli.IntegralModel.Product.bettiQ D.complexAlbanese.X 1
abbrev Data.SphericalPELAlbaneseData.OneFormsA := FormConstants.OneForms D.complexAlbanese.X
abbrev Data.SphericalPELAlbaneseData.OneFormsSpace := FormConstants.OneForms D.complexSpace

def Data.SphericalPELAlbaneseData.pullbackH1Integral (e : D.EndK) : Module.End ℚ D.H1 :=
  PELModuli.IntegralModel.Product.bettiPullbackQ
    ((Over.pullback D.complexGenericPoint).map (TateComparison.End.endSchemeMap D.albaneseGroup.X e)) 1

def Data.SphericalPELAlbaneseData.pullbackForms (e : D.EndK) : D.OneFormsA →ₗ[ℂ] D.OneFormsA :=
  FormConstants.formsPullback
    ((Over.pullback D.complexGenericPoint).map (TateComparison.End.endSchemeMap D.albaneseGroup.X e))

def Data.SphericalPELAlbaneseData.albanesePullback (h : D.HasIntegralModelGeometry) : D.OneFormsA →ₗ[ℂ] D.OneFormsSpace :=
  FormConstants.formsPullback (D.complexAlbaneseMap h)

abbrev Data.SphericalPELAlbaneseData.complexCorrespondence (t : Local.IntegralType s) : Correspondences.EtaleCorrespondence D.complexSpace :=
  (D.correspondence t).baseChange D.complexGenericPoint

/-- Rational pullback means the actual pullback after every valid clearing
of the denominator. Existence of a clearing is included, so this relation
cannot hold vacuously. Additivity and independence are not input fields. -/
def Data.SphericalPELAlbaneseData.IsRationalH1Pullback (e : D.EndQ) (f : Module.End ℚ D.H1) : Prop :=
  (∃ (n : ℕ) (_ : 0 < n) (a : D.EndK), n • e = D.toRational a) ∧
    ∀ (n : ℕ), 0 < n → ∀ a : D.EndK, n • e = D.toRational a →
      (n : ℚ) • f = D.pullbackH1Integral a

@[simp]
theorem Data.SphericalPELAlbaneseData.pullbackH1Integral_one : D.pullbackH1Integral 1 = LinearMap.id := by
  unfold Data.SphericalPELAlbaneseData.pullbackH1Integral
  rw [BaseChange.endSchemeMap_one, CategoryTheory.Functor.map_id, PELModuli.IntegralModel.Product.bettiPullbackQ_id]

theorem Data.SphericalPELAlbaneseData.pullbackH1Integral_mul (a b : D.EndK) :
    D.pullbackH1Integral (a * b) =
      (D.pullbackH1Integral b).comp (D.pullbackH1Integral a) := by
  unfold Data.SphericalPELAlbaneseData.pullbackH1Integral
  rw [BaseChange.endSchemeMap_mul, Functor.map_comp, PELModuli.IntegralModel.Product.bettiPullbackQ_comp]

theorem Data.SphericalPELAlbaneseData.pullbackForms_mul (a b : D.EndK) :
    D.pullbackForms (a * b) = (D.pullbackForms b).comp (D.pullbackForms a) := by
  unfold Data.SphericalPELAlbaneseData.pullbackForms
  rw [BaseChange.endSchemeMap_mul, Functor.map_comp, FormConstants.formsPullback_comp]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison

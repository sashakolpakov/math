import OAI.RepresentationTheory.Theta.Geometric.Complex.PELBaseAction
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Cohomology
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport

/-! # PEL Classification -/

namespace OAI.RepresentationTheory.Theta.Geometric.Complex.PELClassification

noncomputable section

section

/-! TateComparison's actual reduced-test classification constructs a unique point
of the original complex fiber for every genuine complex PEL family. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

def modelComplexPointEquiv :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.complexSpace ≃ (Over.mk D.complexPoint ⟶ D.model.space) :=
  (AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv D.complexGenericPoint (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) D.complexGenericPoint
    (Category.id_comp _) D.space).trans
    (AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv D.generic D.complexGenericPoint D.complexPoint rfl D.model.space)

theorem modelComplexPointEquiv_left (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.complexSpace) :
    (modelComplexPointEquiv D x).left =
      x.left ≫ Limits.pullback.fst D.space.hom D.complexGenericPoint ≫
        Limits.pullback.fst D.model.space.hom D.generic := by
  simp only [modelComplexPointEquiv, Equiv.trans_apply, AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv_left, Category.assoc]

theorem existsUnique_complexPELPoint (hg : D.HasIntegralModelGeometry)
    (C : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (hC : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.IsPELFamily D.reference (Reference.LieSignature.referenceComplexBaseAction D.reference) C) :
    ∃! x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.complexSpace,
      Nonempty (AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso (D.model.family.pullback (modelComplexPointEquiv D x).left) C) := by
  let : IsReduced (Over.mk D.complexPoint).left := inferInstanceAs (IsReduced (Spec (.of ℂ)))
  have hC' : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.IsPELFamily D.reference (D.complexPoint.appTop.hom.comp D.baseAction) C := by
    rw [PELBaseAction.complexPELBaseAction D hg]
    exact hC
  obtain ⟨y, hy, huniq⟩ := hg.classifies.2 (Over.mk D.complexPoint) C hC'
  refine ⟨(modelComplexPointEquiv D).symm y, ?_, ?_⟩
  · simpa only [Equiv.apply_symm_apply] using hy
  · intro x hx
    apply (modelComplexPointEquiv D).injective
    exact (huniq (modelComplexPointEquiv D x) hx).trans
      ((modelComplexPointEquiv D).apply_symm_apply y).symm

end

/-! The actual universal family on a complex test scheme is pulled
back through the original two base changes, with exact fiber formulas. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

def complexModelMap (f : S ⟶ D.complexSpace) :
    Over.mk (S.hom ≫ D.complexPoint) ⟶ D.model.space :=
  AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv D.generic (S.hom ≫ D.complexGenericPoint)
    (S.hom ≫ D.complexPoint) (Category.assoc _ _ _) D.model.space
    (AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv D.complexGenericPoint S.hom (S.hom ≫ D.complexGenericPoint) rfl D.space f)

theorem complexModelMap_left (f : S ⟶ D.complexSpace) :
    (complexModelMap D f).left = f.left ≫ Limits.pullback.fst D.space.hom D.complexGenericPoint ≫
      Limits.pullback.fst D.model.space.hom D.generic := by
  simp only [complexModelMap, AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv_left, Category.assoc]

theorem complexModelMap_point (f : S ⟶ D.complexSpace) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    (modelComplexPointEquiv D (x ≫ f)).left = x.left ≫ (complexModelMap D f).left := by
  rw [modelComplexPointEquiv_left, complexModelMap_left]
  simp only [Over.comp_left, Category.assoc]

def complexUniversalFamily (f : S ⟶ D.complexSpace) :
    AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S.left :=
  D.model.family.pullback (complexModelMap D f).left

theorem complexUniversalFiber_isPEL (hg : D.HasIntegralModelGeometry)
    (f : S ⟶ D.complexSpace) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    (D.model.family.pullback (x.left ≫ (complexModelMap D f).left)).IsPEL D.reference.polarizationType
      (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom := by
  let : IsReduced (Over.mk D.complexPoint).left := inferInstanceAs (IsReduced (Spec (.of ℂ)))
  have h := (hg.classifies.1 (Over.mk D.complexPoint) (modelComplexPointEquiv D (x ≫ f))).1
  rw [complexModelMap_point] at h
  exact h

end

end OAI.RepresentationTheory.Theta.Geometric.Complex.PELClassification

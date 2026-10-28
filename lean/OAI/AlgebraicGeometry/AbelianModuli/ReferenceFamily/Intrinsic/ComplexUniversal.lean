import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.BallPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FinePELPointClassification

/-! # Complex Universal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The actual universal PEL object pulls back to every complex test
family, with its base map agreeing exactly with the native point map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}

def Intrinsic.ComplexUniversal.complexPointRestriction (κ : K →+* ℂ) {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    Over.mk (Spec.map (CommRingCat.ofHom κ)) ⟶ Complex.BallPeriods.restrictComplexBase κ S :=
  Over.homMk y.left (Complex.BallPeriods.restrictComplexBase_point κ y)

variable (M : Models.FinePELModel P iota N) (κ : K →+* ℂ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ)

def Models.FinePELModel.complexFamilyBaseMap : Complex.BallPeriods.restrictComplexBase κ S ⟶ M.space :=
  Over.homMk (f.left ≫ pullback.fst M.space.hom (Spec.map (CommRingCat.ofHom κ))) (by
    change (f.left ≫ pullback.fst M.space.hom (Spec.map (CommRingCat.ofHom κ))) ≫ M.space.hom =
      S.hom ≫ Spec.map (CommRingCat.ofHom κ)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun a => f.left ≫ a) (pullback.condition (f := M.space.hom)
        (g := Spec.map (CommRingCat.ofHom κ)))).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun a => a ≫ Spec.map (CommRingCat.ofHom κ)) f.w))))

def Models.FinePELModel.complexTestFamily : PEL.Objects.PELObject P iota N (Complex.BallPeriods.restrictComplexBase κ S) :=
  M.universal.pullback (M.complexFamilyBaseMap κ f)

theorem Models.FinePELModel.complexFamilyBaseMap_point (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    Intrinsic.ComplexUniversal.complexPointRestriction κ y ≫ M.complexFamilyBaseMap κ f =
      M.complexPointBaseEquiv κ (y ≫ f) := by
  apply Over.OverMorphism.ext
  exact (Category.assoc y.left f.left (pullback.fst M.space.hom (Spec.map (CommRingCat.ofHom κ)))).symm

theorem Models.FinePELModel.complexTestFamily_point_class (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    ((M.complexTestFamily κ f).pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ y)).classOf =
      (M.universal.pullback (M.complexPointBaseEquiv κ (y ≫ f))).classOf := by
  have h : (M.universal.pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ y ≫ M.complexFamilyBaseMap κ f)).classOf =
      ((M.complexTestFamily κ f).pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ y)).classOf :=
    Quotient.sound ⟨PEL.Objects.PELIso.pullbackComp M.universal (M.complexFamilyBaseMap κ f) (Intrinsic.ComplexUniversal.complexPointRestriction κ y)⟩
  rw [M.complexFamilyBaseMap_point] at h
  exact h.symm

theorem Models.FinePELModel.point_eq_of_complexTestFamily_iso (hM : M.IsFine) (y z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (e : PEL.Objects.PELIso ((M.complexTestFamily κ f).pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ y))
      ((M.complexTestFamily κ f).pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ z))) : y ≫ f = z ≫ f := by
  apply (M.complexPointClassEquiv κ hM).injective
  change (M.universal.pullback (M.complexPointBaseEquiv κ (y ≫ f))).classOf =
    (M.universal.pullback (M.complexPointBaseEquiv κ (z ≫ f))).classOf
  rw [← M.complexTestFamily_point_class κ f y, ← M.complexTestFamily_point_class κ f z]
  exact Quotient.sound ⟨e⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

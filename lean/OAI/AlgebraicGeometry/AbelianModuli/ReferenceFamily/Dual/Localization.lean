import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PresentedAlgebra
import OAI.AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints

/-! # Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Localization

noncomputable section

/-! Actual dual-number points extend uniquely to a principal open
neighborhood of their reduction, so the tangent construction is local. -/

open OAI.AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic

variable {S : Type*} [CommRing S] [Algebra ℂ S]

def localizeDualPoint (x : S →ₐ[ℂ] ℂ) (g : S) (hg : x g ≠ 0) (f : PresentedAlgebra.DualAlgebraPoints x) :
    Localization.Away g →ₐ[ℂ] DualNumber ℂ :=
  IsLocalization.Away.liftAlgHom (S := Localization.Away g) (f := f.val) g
    (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
      (isUnit_iff_ne_zero.mpr (fun h => hg
        ((DFunLike.congr_fun f.property g).symm.trans h))))

theorem localizeDualPoint_algebraMap (x : S →ₐ[ℂ] ℂ) (g : S) (hg : x g ≠ 0)
    (f : PresentedAlgebra.DualAlgebraPoints x) (a : S) :
    localizeDualPoint x g hg f (algebraMap S (Localization.Away g) a) = f.val a := by
  simp [localizeDualPoint]

theorem localizeDualPoint_reduction (x : S →ₐ[ℂ] ℂ) (g : S) (hg : x g ≠ 0)
    (f : PresentedAlgebra.DualAlgebraPoints x) :
    (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp (localizeDualPoint x g hg f) = Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x g hg := by
  apply IsLocalization.algHom_ext (Submonoid.powers g)
  apply AlgHom.ext
  intro a
  exact (congrArg TrivSqZeroExt.fst (localizeDualPoint_algebraMap x g hg f a)).trans
    ((DFunLike.congr_fun f.property a).trans (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_algebraMap x g hg a).symm)

def dualLocalizationEquiv (x : S →ₐ[ℂ] ℂ) (g : S) (hg : x g ≠ 0) :
    PresentedAlgebra.DualAlgebraPoints x ≃ PresentedAlgebra.DualAlgebraPoints (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x g hg) where
  toFun f := ⟨localizeDualPoint x g hg f, localizeDualPoint_reduction x g hg f⟩
  invFun f := ⟨f.val.comp (Algebra.algHom ℂ S (Localization.Away g)), by
    apply AlgHom.ext
    intro a
    exact (DFunLike.congr_fun f.property (algebraMap S (Localization.Away g) a)).trans
      (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_algebraMap x g hg a)⟩
  left_inv f := by
    apply Subtype.ext
    apply AlgHom.ext
    intro a
    exact localizeDualPoint_algebraMap x g hg f a
  right_inv f := by
    apply Subtype.ext
    apply IsLocalization.algHom_ext (Submonoid.powers g)
    apply AlgHom.ext
    intro a
    exact localizeDualPoint_algebraMap x g hg _ a

def dualLocalizationRestrictionEquiv (g : S) (y : Localization.Away g →ₐ[ℂ] ℂ) :
    PresentedAlgebra.DualAlgebraPoints y ≃ PresentedAlgebra.DualAlgebraPoints (y.comp (Algebra.algHom ℂ S (Localization.Away g))) := by
  let x := y.comp (Algebra.algHom ℂ S (Localization.Away g))
  have hx : x g ≠ 0 := isUnit_iff_ne_zero.mp
    ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).map y)
  have hy : Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x g hx = y := (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_unique x g hx y rfl).symm
  let e : PresentedAlgebra.DualAlgebraPoints y ≃ PresentedAlgebra.DualAlgebraPoints (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x g hx) :=
    Set.equivOfEq (congrArg (fun z => {f : Localization.Away g →ₐ[ℂ] DualNumber ℂ |
      (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp f = z}) hy.symm)
  exact e.trans (dualLocalizationEquiv x g hx).symm

theorem dualLocalizationRestrictionEquiv_apply (g : S) (y : Localization.Away g →ₐ[ℂ] ℂ)
    (f : PresentedAlgebra.DualAlgebraPoints y) (a : S) :
    (dualLocalizationRestrictionEquiv g y f).val a =
      f.val (algebraMap S (Localization.Away g) a) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Localization

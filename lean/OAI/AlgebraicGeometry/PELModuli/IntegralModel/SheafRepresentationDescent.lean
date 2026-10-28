import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RestrictedClassifyingEquiv
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SheafBaseChangeConservative
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-! # Sheaf Representation Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SheafRepresentationDescent

noncomputable section

/-! A global element represents a sheaf if its restriction is the
universal element of an actual local representation on an fppf base cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem sheaf_isRepresentedBy_of_fppf_restriction {S T : Scheme.{u}}
    (b : T ⟶ S) [Flat b] [Surjective b] [LocallyOfFinitePresentation b]
    (D : Over S) (F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
    (x : F.obj.obj (.op D))
    (R : ((Over.map b).op ⋙ F.obj).RepresentableBy ((Over.pullback b).obj D))
    (hx : R.homEquiv (𝟙 ((Over.pullback b).obj D)) =
      F.obj.map ((Over.mapPullbackAdj b).counit.app D).op x) :
    F.obj.IsRepresentedBy x := by
  let J := Scheme.fppfTopology.over S
  let φ : (GrothendieckTopology.uliftYoneda.{u + 1} J).obj D ⟶ F := J.uliftYonedaEquiv.symm x
  let φ' := (Scheme.fppfTopology.overMapPullback (Type (u + 1)) b).map φ
  have hφ' : IsIso φ' := by
    have hcomp : ∀ W, IsIso (φ'.hom.app W) := by
      intro W
      apply (isIso_iff_bijective _).mpr
      have he := (RestrictedClassifyingEquiv.restrictedClassifyingEquiv b D F.obj R W.unop).bijective.comp
        (Equiv.ulift.{u + 1}).bijective
      have hm : ⇑(φ'.hom.app W) = fun a => RestrictedClassifyingEquiv.restrictedClassifyingEquiv b D F.obj R W.unop a.down := by
        funext a
        exact (RestrictedClassifyingEquiv.restrictedClassifyingEquiv_apply b D F.obj x R hx W.unop a.down).symm
      rwa [hm]
    have : IsIso ((sheafToPresheaf _ _).map φ') := NatIso.isIso_of_isIso_app φ'.hom
    exact isIso_of_reflects_iso φ' (sheafToPresheaf _ _)
  have : IsIso φ := SheafBaseChangeConservative.sheaf_isIso_of_fppf_baseChange b φ
  constructor
  intro Y
  exact ((isIso_iff_bijective (φ.hom.app (.op Y))).mp inferInstance).comp Equiv.ulift.symm.bijective

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SheafRepresentationDescent

import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.LinearHom
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation

/-! # Hom Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomEvaluation

noncomputable section

/-! The affine Hom comparison evaluates the original local sheaf map.
Its compatibility with restriction is the naturality of that map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)

abbrev evaluation := ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen M N U

theorem restriction {V : X.Opens} (i : V ⟶ U)
    (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U)) (m : Γ(M, U)) :
    evaluation M N V ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N).presheaf.map i.op q)
        (M.presheaf.map i.op m) =
      N.presheaf.map i.op (evaluation M N U q m) := by
  let j : Over.mk i ⟶ Over.mk (𝟙 U) := Over.homMk i
  exact congrArg (fun a => a m) (q.val.naturality j.op)

abbrev chartEvaluation (hU : IsAffineOpen U)
    (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U)) :
    (AffineOpen.InternalHom.sections U hU).obj M ⟶
      (AffineOpen.InternalHom.sections U hU).obj N :=
  (AffineOpen.LinearHom.comparison U hU N).app (op M) q

abbrev chartImage (hU : IsAffineOpen U) : X.Opens :=
  U.ι ''ᵁ (hU.isoSpec.inv ''ᵁ ⊤)

theorem chartImage_eq (hU : IsAffineOpen U) : chartImage U hU = U := by
  rw [chartImage, ← Scheme.Hom.comp_image]
  exact ChartSections.image_top U hU

theorem chartIso_apply (hU : IsAffineOpen U) (m : Γ(M, U)) :
    (ChartSections.iso U hU M).hom m =
      M.presheaf.map (eqToHom (chartImage_eq U hU)).op m := by
  let a := (eqToHom (ChartSections.image_top U hU)).op
  let b : op (hU.fromSpec ''ᵁ ⊤) ⟶ op (chartImage U hU) :=
    (eqToHom (Scheme.Hom.comp_image hU.isoSpec.inv U.ι ⊤).symm).op
  change M.presheaf.map b (M.presheaf.map a m) = _
  have he : a ≫ b = (eqToHom (chartImage_eq U hU)).op := Subsingleton.elim _ _
  exact (ConcreteCategory.congr_hom (M.presheaf.map_comp a b) m).symm.trans
    (congrArg (fun t => M.presheaf.map t m) he)

theorem chart_comparison_apply (hU : IsAffineOpen U)
    (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U)) (m : Γ(M, U)) :
    chartEvaluation M N U hU q
        ((ChartSections.iso U hU M).hom m) =
      (ChartSections.iso U hU N).hom (evaluation M N U q m) := by
  change q.val.app (op (Over.mk (eqToHom (chartImage_eq U hU))))
      ((ChartSections.iso U hU M).hom m) = _
  rw [chartIso_apply, chartIso_apply]
  let i := eqToHom (chartImage_eq U hU)
  let j : Over.mk i ⟶ Over.mk (𝟙 U) := Over.homMk i
  exact congrArg (fun a => a m) (q.val.naturality j.op)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomEvaluation

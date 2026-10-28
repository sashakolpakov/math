import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.FunctionalNe
import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi

/-! # Functional Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.FunctionalDescent

noncomputable section

/-! Scalar algebraization descends through an epimorphic family of actual
algebraic line bundles. Native regular evaluation is a monomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

def nativeStructureEvaluation : FunctionalNe.HolomorphicScalarFunctional V (HilbertConstruction.Line.Bundles.structureModule V.carrier) :=
  SheafOfModules.unitToPushforwardObjUnit
    (F := Opens.map (DivisorClass.Chern.Holomorphic.RegularEvaluation.holomorphicAnalytificationPointMap V)) (DivisorClass.Chern.Holomorphic.RegularEvaluation.algebraicToHolomorphicStructureSheaf V)

theorem holomorphicScalarFunctionalOfAlgebraic_injective (M : V.carrier.Modules) :
    Function.Injective (FunctionalNe.holomorphicScalarFunctionalOfAlgebraic V (M := M)) := by
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  intro f g he
  apply Scheme.Modules.hom_ext
  intro U
  ext z
  apply RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections.complexSectionValue_ext V.toOver U
  intro x hx
  have hc := congrArg (fun q : FunctionalNe.HolomorphicScalarFunctional V M => q.onSection U z ⟨x, hx⟩) he
  exact (Intrinsic.FrameEvaluation.sectionEvaluationOn_native V.presentation U (f.app U z) ⟨x, hx⟩).symm.trans
    (hc.trans (Intrinsic.FrameEvaluation.sectionEvaluationOn_native V.presentation U (g.app U z) ⟨x, hx⟩))

instance nativeStructureEvaluation_mono : Mono (nativeStructureEvaluation V) where
  right_cancellation {Z} _f _g h := holomorphicScalarFunctionalOfAlgebraic_injective V Z h

theorem exists_algebraic_scalarFunctional_of_line_generators
    (M : V.carrier.Modules) {I : Type} (L : I → HilbertConstruction.Line.Bundles.LineBundle V.carrier)
    (s : ∀ i, (L i).sheaf ⟶ M) [Epi (Sigma.desc s)] (f : FunctionalNe.HolomorphicScalarFunctional V M) :
    ∃ g : M ⟶ HilbertConstruction.Line.Bundles.structureModule V.carrier, FunctionalNe.holomorphicScalarFunctionalOfAlgebraic V g = f := by
  have h : ∀ i, ∃ g : (L i).sheaf ⟶ HilbertConstruction.Line.Bundles.structureModule V.carrier,
      FunctionalNe.holomorphicScalarFunctionalOfAlgebraic V g = s i ≫ f :=
    fun i => FunctionalNe.HolomorphicScalarFunctional.exists_algebraic (L := L i) (s i ≫ f)
  choose g hg using h
  have hc : Sigma.desc g ≫ nativeStructureEvaluation V = Sigma.desc s ≫ f := by
    apply Sigma.hom_ext
    intro i
    exact (Sigma.ι_comp_desc_assoc g i (nativeStructureEvaluation V)).trans
      ((hg i).trans (Sigma.ι_comp_desc_assoc s i f).symm)
  let sq : CommSq (Sigma.desc g) (Sigma.desc s) (nativeStructureEvaluation V) f := ⟨hc⟩
  let : StrongEpi (Sigma.desc s) := strongEpi_of_epi (Sigma.desc s)
  exact ⟨sq.lift, sq.fac_right⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.FunctionalDescent

import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.TorsorPullback
import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegerGeneratorInverseImage
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Inverse Image -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: the torsor of the actual pulled-back extension

Exact inverse image preserves the defining fiber over the integer generator.
The comparison uses the original coefficient and constant-sheaf maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {ℓ n : ℕ} {X Y : Scheme.{u}} (E : App.Construction.FiniteCoefficientExtension ℓ n Y) (f : X ⟶ Y)

/-- Compatibility of the pulled-back extension projection on underlying sheaves. -/
theorem App.Construction.FiniteCoefficientExtension.pullbackProjection_underlying :
    (ProEtale.PullbackTypes.Construction.proEtTypeSheafPullback f).map
      ((sheafCompose (Scheme.ProEt.topology Y) (forget Ab.{u + 1})).map E.projection) ≫
        (IntegerGeneratorInverseImage.Construction.proEtIntegerPullbackUnderlyingIso f).hom =
    (ProEtale.PullbackTypes.Construction.proEtPullbackForgetIso f).inv.app E.middle ≫
      (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).map
        (E.pullbackExtension f).projection := by
  change (ProEtale.PullbackTypes.Construction.proEtTypeSheafPullback f).map
      ((sheafCompose (Scheme.ProEt.topology Y) (forget Ab.{u + 1})).map E.projection) ≫
    ((ProEtale.PullbackTypes.Construction.proEtPullbackForgetIso f).inv.app (ProetalePullback.Construction.proEtIntegerConstant Y) ≫
      (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).map
        ((ProetalePullback.Construction.proEtConstantPullbackIso f).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) =
    (ProEtale.PullbackTypes.Construction.proEtPullbackForgetIso f).inv.app E.middle ≫
      (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).map
        ((ProetalePullback.Construction.proEtSheafPullback f).map E.projection ≫
          (ProetalePullback.Construction.proEtConstantPullbackIso f).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  exact (ProEtale.PullbackTypes.Construction.proEtPullbackForgetIso f).inv.naturality E.projection

/-- Inverse image of the original torsor is the fiber defining the pulled-back extension. -/
theorem App.Construction.FiniteCoefficientExtension.inverseImageFiber_isPullback :
    IsPullback
      ((ProEtale.PullbackTypes.Construction.proEtTypeSheafPullback f).map E.fiberInclusion ≫
        (ProEtale.PullbackTypes.Construction.proEtPullbackForgetIso f).inv.app E.middle)
      (terminal.from ((ProEtale.PullbackTypes.Construction.proEtTypeSheafPullback f).obj E.fiberSheaf))
      ((sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).map
        (E.pullbackExtension f).projection)
      (FiberPullback.Construction.proEtIntegerGeneratorMap X) := by
  let t := (terminalIsTerminal.isTerminalObj (ProEtale.PullbackTypes.Construction.proEtTypeSheafPullback f)
    (⊤_ (Sheaf (Scheme.ProEt.topology Y) (Type (u + 1))))).uniqueUpToIso terminalIsTerminal
  apply (E.fiberSheaf_isPullback.map (ProEtale.PullbackTypes.Construction.proEtTypeSheafPullback f)).of_iso
    (Iso.refl _) ((ProEtale.PullbackTypes.Construction.proEtPullbackForgetIso f).app E.middle).symm t
    (IntegerGeneratorInverseImage.Construction.proEtIntegerPullbackUnderlyingIso f)
  · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
    rfl
  · exact terminalIsTerminal.hom_ext _ _
  · exact E.pullbackProjection_underlying f
  · rw [IntegerGeneratorInverseImage.Construction.proEtIntegerGeneratorMap_pullback]
    congr 1

/-- The actual inverse image of the original torsor sheaf is its pulled-back extension's torsor. -/
def App.Construction.FiniteCoefficientExtension.inverseImageFiberIso :
    (ProEtale.PullbackTypes.Construction.proEtTypeSheafPullback f).obj E.fiberSheaf ≅ (E.pullbackExtension f).fiberSheaf :=
  (E.inverseImageFiber_isPullback f).isoIsPullback _ _
    (E.pullbackExtension f).fiberSheaf_isPullback

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

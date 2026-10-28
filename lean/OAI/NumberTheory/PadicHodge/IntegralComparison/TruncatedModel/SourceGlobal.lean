import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverCoefficientCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSheafValue
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelTopCoverComparison

/-! # Source Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceGlobal

noncomputable section

/-! The original single-sheaf output coordinate has the original
native global top-cover value, on any genuine cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem cancel_coordinates {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B S : C} {T : D} (a : A ⟶ B) (e : S ≅ B) (b : F.obj B ⟶ T) :
    F.map (a ≫ e.inv) ≫ (F.map e.hom ≫ b) = F.map a ≫ b := by
  rw [← Category.assoc, ← F.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (g c : ℕ) [SmoothOfRelativeDimension g X.hom]
  {ι : Type} [LinearOrder ι] (U : ι → X.left.Opens) (hU : iSup U = ⊤)

abbrev form := TopCover.form p k n X g
abbrev lift := AdditiveTop.Comparison.lift

private theorem lift_apply {A B : AddCommGrpCat.{0}} {T : AddCommGrpCat.{2}}
    (a : A ⟶ B) (b : lift.obj B ⟶ T) (d : lift.obj A ⟶ T)
    (h : lift.map a ≫ b = d) (x : A) :
    b (ULift.up.{2,1} (ULift.up.{1,0} (a x))) =
      d (ULift.up.{2,1} (ULift.up.{1,0} x)) :=
  ConcreteCategory.congr_hom h (ULift.up.{2,1} (ULift.up.{1,0} x))

abbrev sourceCoordinates :=
  ((ModuleCech.CohomologyNaturality.forgetHomologyIso
      (Truncated.Witt.Ring p k n) X U (form p k n X g) g).hom ≫
    homologyMap (OrderedCech.Projection.map U (form p k n X g).presheaf) g) ≫
      (PrincipalSheafValue.globalCoordinates p k n X g c U).inv

theorem comparison :
    lift.map (sourceCoordinates p k n X g c U) ≫
      PrincipalSheafValue.globalValue p k n X Y f hp I g c U hU =
    ModelTopCoverComparison.globalInput p k n X Y f hp I g U hU := by
  have hc := cancel_coordinates lift
    ((ModuleCech.CohomologyNaturality.forgetHomologyIso
      (Truncated.Witt.Ring p k n) X U (form p k n X g) g).hom ≫
      homologyMap (OrderedCech.Projection.map U (form p k n X g).presheaf) g)
    (PrincipalSheafValue.globalCoordinates p k n X g c U)
    ((PrincipalSheafValue.globalCoefficientIso p k n X g U).hom ≫
      TopCover.globalMap p k n X Y f hp I g U hU)
  have hi := congrArg (fun a => a ≫
      TopCover.globalMap p k n X Y f hp I g U hU)
    (TopCoverCoefficientCoordinates.comparison p k n X g U)
  exact hc.trans ((Category.assoc _ _ _).symm.trans hi)

attribute [local irreducible] HomologicalComplex.homology

theorem comparison_apply
    (x : IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X U g) :
    PrincipalSheafValue.globalValue p k n X Y f hp I g c U hU
      (ULift.up.{2,1} (ULift.up.{1,0} (sourceCoordinates p k n X g c U x))) =
    ModelTopCoverComparison.globalInput p k n X Y f hp I g U hU
      (ULift.up.{2,1} (ULift.up.{1,0} x)) :=
  lift_apply (sourceCoordinates p k n X g c U)
    (PrincipalSheafValue.globalValue p k n X Y f hp I g c U hU)
    (ModelTopCoverComparison.globalInput p k n X Y f hp I g U hU)
    (comparison p k n X Y f hp I g c U hU) x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceGlobal

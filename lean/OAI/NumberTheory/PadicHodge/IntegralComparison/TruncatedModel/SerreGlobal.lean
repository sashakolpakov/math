import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FiniteEtaleSourceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormSourceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.RefinedTransferTrace

/-! # Serre Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SerreGlobal

noncomputable section

/-! Original Serre classes enter the native global top map through
exactly the original source-output coordinates, on the projective cover
and its finite inverse image. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem inverse_output {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B S : C} {T : D} (e : A ≅ B)
    (a : B ⟶ S) (s : A ⟶ S) (v : F.obj S ⟶ T) (b : F.obj A ⟶ T)
    (hs : e.hom ≫ a = s) (hv : F.map s ≫ v = b) :
    F.map a ≫ v = F.map e.inv ≫ b := by
  have h : e.inv ≫ s = a := by
    rw [← hs, Iso.inv_hom_id_assoc]
  rw [← h, F.map_comp, Category.assoc, hv]

private theorem lift_square_apply {A B C : AddCommGrpCat.{0}} {T : AddCommGrpCat.{2}}
    (a : A ⟶ B) (c : A ⟶ C)
    (b : AdditiveTop.Comparison.lift.obj B ⟶ T)
    (d : AdditiveTop.Comparison.lift.obj C ⟶ T)
    (h : AdditiveTop.Comparison.lift.map a ≫ b =
      AdditiveTop.Comparison.lift.map c ≫ d) (x : A) :
    b (ULift.up.{2,1} (ULift.up.{1,0} (a x))) =
      d (ULift.up.{2,1} (ULift.up.{1,0} (c x))) :=
  ConcreteCategory.congr_hom h (ULift.up.{2,1} (ULift.up.{1,0} x))

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) [IsNoetherianRing (Truncated.Witt.Ring p k n)]
  [IsArtinianRing (Truncated.Witt.Ring p k n)] [IsLocalRing (Truncated.Witt.Ring p k n)]
  [Module.Injective (Truncated.Witt.Ring p k n) (Truncated.Witt.Ring p k n)] {d : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

namespace Finite
variable (X Y : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Nonempty X.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [Smooth Y.hom] [IsProper Y.hom] [Y.left.IsSeparated]
  (f : Y ⟶ X) [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1)) [IsClosedImmersion i.left]
  (Z : Over (Spec (CommRingCat.of k))) [IsSeparated Z.hom] (j : Z.left ⟶ Y.left)
  (hp : IsPullback j Z.hom Y.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Z) n))
  (g c : ℕ) [SmoothOfRelativeDimension g X.hom] [SmoothOfRelativeDimension g Y.hom]

abbrev cover := Intrinsic.FiniteEtaleSourceCoordinates.sourceCover X Y f i
abbrev coverFull := Intrinsic.RefinedTransferTrace.inverseCover_top
  (Truncated.Witt.Ring p k n) Y X f (Intrinsic.TopFormTrace.cover X i)
  (Intrinsic.TopFormTrace.cover_top X i)
abbrev output := PrincipalReference.Source.ReferenceComparison.sourceOutput f.left i.left
  (Projective.IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1)).hom
  (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := Truncated.Witt.Ring p k n) (σ := Fin (d+2)))
  (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) Y g) c g

omit [Fintype k] [CharP k p] [IsNoetherianRing (Truncated.Witt.Ring p k n)] [IsArtinianRing (Truncated.Witt.Ring p k n)] [IsLocalRing (Truncated.Witt.Ring p k n)] [Module.Injective (Truncated.Witt.Ring p k n) (Truncated.Witt.Ring p k n)] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [Smooth Y.hom] [IsProper Y.hom] [Y.left.IsSeparated] [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [IsClosedImmersion (Over.Hom.left i)] [SmoothOfRelativeDimension g X.hom] [SmoothOfRelativeDimension g Y.hom] in
theorem source_comparison :
    (Intrinsic.EtaleProperTraceBase.IntrinsicFinite.serreIso X Y f i g).hom ≫ output p k n X Y f i g c =
      SourceGlobal.sourceCoordinates p k n Y g c (cover p k n X Y f i) := by
  have h := Intrinsic.FiniteEtaleSourceCoordinates.comparison X Y f i c g
  dsimp only [Intrinsic.FiniteEtaleSourceCoordinates.sourceCoordinates] at h
  simp only [SourceGlobal.sourceCoordinates, Category.assoc]
  convert h using 1 ; (as_aux_lemma => rfl)

omit [IsNoetherianRing (Truncated.Witt.Ring p k n)] [IsArtinianRing (Truncated.Witt.Ring p k n)] [IsLocalRing (Truncated.Witt.Ring p k n)] [Module.Injective (Truncated.Witt.Ring p k n) (Truncated.Witt.Ring p k n)] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [IsClosedImmersion (Over.Hom.left i)] [SmoothOfRelativeDimension g X.hom] in
theorem comparison :
    AdditiveTop.Comparison.lift.map (output p k n X Y f i g c) ≫
      PrincipalSheafValue.globalValue p k n Y Z j hp I g c
        (cover p k n X Y f i) (coverFull p k n X Y f i) =
    AdditiveTop.Comparison.lift.map (Intrinsic.EtaleProperTraceBase.IntrinsicFinite.serreIso X Y f i g).inv ≫
      ModelTopCoverComparison.globalInput p k n Y Z j hp I g
        (cover p k n X Y f i) (coverFull p k n X Y f i) :=
  inverse_output AdditiveTop.Comparison.lift
    (Intrinsic.EtaleProperTraceBase.IntrinsicFinite.serreIso X Y f i g) _ _ _ _
    (source_comparison p k n X Y f i g c)
    (SourceGlobal.comparison p k n Y Z j hp I g c
      (cover p k n X Y f i) (coverFull p k n X Y f i))

section Pointwise
attribute [local irreducible] HomologicalComplex.homology

omit [IsNoetherianRing (Truncated.Witt.Ring p k n)] [IsArtinianRing (Truncated.Witt.Ring p k n)] [IsLocalRing (Truncated.Witt.Ring p k n)] [Module.Injective (Truncated.Witt.Ring p k n) (Truncated.Witt.Ring p k n)] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [IsClosedImmersion (Over.Hom.left i)] [SmoothOfRelativeDimension g X.hom] in
theorem comparison_apply (x : FiniteEtale.ProperTraceBase.cohomology X Y f i g) :
    PrincipalSheafValue.globalValue p k n Y Z j hp I g c
      (cover p k n X Y f i) (coverFull p k n X Y f i)
      (ULift.up.{2,1} (ULift.up.{1,0} (output p k n X Y f i g c x))) =
    ModelTopCoverComparison.globalInput p k n Y Z j hp I g
      (cover p k n X Y f i) (coverFull p k n X Y f i)
      (ULift.up.{2,1} (ULift.up.{1,0} ((Intrinsic.EtaleProperTraceBase.IntrinsicFinite.serreIso X Y f i g).inv x))) :=
  lift_square_apply (output p k n X Y f i g c)
    (Intrinsic.EtaleProperTraceBase.IntrinsicFinite.serreIso X Y f i g).inv
    (PrincipalSheafValue.globalValue p k n Y Z j hp I g c
      (cover p k n X Y f i) (coverFull p k n X Y f i))
    (ModelTopCoverComparison.globalInput p k n Y Z j hp I g
      (cover p k n X Y f i) (coverFull p k n X Y f i))
    (comparison p k n X Y f i Z j hp I g c) x
end Pointwise

abbrev bounded_comparison_apply (x : FiniteEtale.ProperTraceBase.cohomology X Y f i g) :=
  congrArg (AdditiveGlobal.globalHomologyIso p k n Y Z j I (g+g)).hom
    (comparison_apply p k n X Y f i Z j hp I g c x)
end Finite

namespace Smooth
variable (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Nonempty X.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [X.left.IsSeparated]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1)) [IsClosedImmersion i.left]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (g c : ℕ) [SmoothOfRelativeDimension g X.hom]

abbrev cover := Intrinsic.TopFormTrace.cover X i
abbrev coverFull := Intrinsic.TopFormTrace.cover_top X i
abbrev output := PrincipalReference.Source.ReferenceComparison.sourceOutput (𝟙 X.left) i.left
  (Projective.IntrinsicOverlap.Intrinsic.model (Truncated.Witt.Ring p k n) (d+1)).hom
  (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := Truncated.Witt.Ring p k n) (σ := Fin (d+2)))
  (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g) c g

omit [Fintype k] [CharP k p] [IsNoetherianRing (Truncated.Witt.Ring p k n)] [IsArtinianRing (Truncated.Witt.Ring p k n)] [IsLocalRing (Truncated.Witt.Ring p k n)] [Module.Injective (Truncated.Witt.Ring p k n) (Truncated.Witt.Ring p k n)] [Nonempty ↥X.left] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [X.left.IsSeparated] [IsClosedImmersion (Over.Hom.left i)] [SmoothOfRelativeDimension g X.hom] in
theorem source_comparison :
    (Intrinsic.TopFormTrace.serreIso X i g).hom ≫ output p k n X i g c =
      SourceGlobal.sourceCoordinates p k n X g c (cover p k n X i) := by
  have h := Intrinsic.TopFormSourceCoordinates.comparison X i c g
  dsimp only [Intrinsic.TopFormSourceCoordinates.sourceCoordinates] at h
  simp only [SourceGlobal.sourceCoordinates, Category.assoc]
  convert h using 1 ; (as_aux_lemma => rfl)

omit [IsNoetherianRing (Truncated.Witt.Ring p k n)] [IsArtinianRing (Truncated.Witt.Ring p k n)] [IsLocalRing (Truncated.Witt.Ring p k n)] [Module.Injective (Truncated.Witt.Ring p k n) (Truncated.Witt.Ring p k n)] [Nonempty ↥X.left] [GeometricallyConnected X.hom] [IsClosedImmersion (Over.Hom.left i)] in
theorem comparison :
    AdditiveTop.Comparison.lift.map (output p k n X i g c) ≫
      PrincipalSheafValue.globalValue p k n X Y f hp I g c
        (cover p k n X i) (coverFull p k n X i) =
    AdditiveTop.Comparison.lift.map (Intrinsic.TopFormTrace.serreIso X i g).inv ≫
      ModelTopCoverComparison.globalInput p k n X Y f hp I g
        (cover p k n X i) (coverFull p k n X i) :=
  inverse_output AdditiveTop.Comparison.lift
    (Intrinsic.TopFormTrace.serreIso X i g) _ _ _ _
    (source_comparison p k n X i g c)
    (SourceGlobal.comparison p k n X Y f hp I g c
      (cover p k n X i) (coverFull p k n X i))

section Pointwise
attribute [local irreducible] HomologicalComplex.homology

omit [IsNoetherianRing (Truncated.Witt.Ring p k n)] [IsArtinianRing (Truncated.Witt.Ring p k n)] [IsLocalRing (Truncated.Witt.Ring p k n)] [Module.Injective (Truncated.Witt.Ring p k n) (Truncated.Witt.Ring p k n)] [Nonempty ↥X.left] [GeometricallyConnected X.hom] [IsClosedImmersion (Over.Hom.left i)] in
theorem comparison_apply (x : IntegralComparison.Smooth.ProjectiveFormTrace.cohomology X i g) :
    PrincipalSheafValue.globalValue p k n X Y f hp I g c
      (cover p k n X i) (coverFull p k n X i)
      (ULift.up.{2,1} (ULift.up.{1,0} (output p k n X i g c x))) =
    ModelTopCoverComparison.globalInput p k n X Y f hp I g
      (cover p k n X i) (coverFull p k n X i)
      (ULift.up.{2,1} (ULift.up.{1,0} ((Intrinsic.TopFormTrace.serreIso X i g).inv x))) :=
  lift_square_apply (output p k n X i g c)
    (Intrinsic.TopFormTrace.serreIso X i g).inv
    (PrincipalSheafValue.globalValue p k n X Y f hp I g c
      (cover p k n X i) (coverFull p k n X i))
    (ModelTopCoverComparison.globalInput p k n X Y f hp I g
      (cover p k n X i) (coverFull p k n X i))
    (comparison p k n X i Y f hp I g c) x
end Pointwise

abbrev bounded_comparison_apply (x : IntegralComparison.Smooth.ProjectiveFormTrace.cohomology X i g) :=
  congrArg (AdditiveGlobal.globalHomologyIso p k n X Y f I (g+g)).hom
    (comparison_apply p k n X i Y f hp I g c x)
end Smooth

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SerreGlobal

import OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorMonoidal
import OAI.AlgebraicGeometry.SheafCohomology.Projective.EquivalenceRightAdjointMate
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorEquivalence
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafTensor

/-! # Line Bundle Projection Formula -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleProjectionFormula.Construction

noncomputable section

/-! The pushforward projection formula for an actual line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u v

def tensorRightEquivalenceOfInverse
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (M N : C) (e : M ⊗ N ≅ 𝟙_ C) (f : N ⊗ M ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorRight M) (tensorRight N)
    ((tensorRightTensor M N).symm ≪≫ (tensoringRight C).mapIso e ≪≫
      rightUnitorNatIso C).symm
    ((tensorRightTensor N M).symm ≪≫ (tensoringRight C).mapIso f ≪≫
      rightUnitorNatIso C)

def lineBundleProjectionFormula {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (M : X.Modules) :
    SheafTensor.Construction.sheafTensor ((Scheme.Modules.pushforward f).obj M) L.sheaf ≅
      (Scheme.Modules.pushforward f).obj
        (SheafTensor.Construction.sheafTensor M ((Scheme.Modules.pullback f).obj L.sheaf)) := by
  letI := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X
  letI := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory Y
  letI := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.symmetricCategory X
  letI := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.symmetricCategory Y
  letI := AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f
  let P := L.sheaf
  let N := AlgebraicGeometry.SheafCohomology.Projective.Dual.Scheme.Modules.dualObj P
  let ePN : P ⊗ N ≅ 𝟙_ Y.Modules :=
    AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalTensorObjIso P N ≪≫
      AlgebraicGeometry.SheafCohomology.Projective.InvertibleEvaluation.Scheme.Modules.invertibleEvaluationIso (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L) ≪≫
        (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso Y).symm
  let eNP : N ⊗ P ≅ 𝟙_ Y.Modules := (β_ _ _) ≪≫ ePN
  let E := tensorRightEquivalenceOfInverse P N ePN eNP
  let P' := (Scheme.Modules.pullback f).obj P
  let N' := (Scheme.Modules.pullback f).obj N
  let ep : P' ⊗ N' ≅ 𝟙_ X.Modules :=
    Functor.Monoidal.μIso (Scheme.Modules.pullback f) P N ≪≫
      (Scheme.Modules.pullback f).mapIso ePN ≪≫
        (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).symm
  let en : N' ⊗ P' ≅ 𝟙_ X.Modules := (β_ _ _) ≪≫ ep
  let E' := tensorRightEquivalenceOfInverse P' N' ep en
  let h : E.inverse ⋙ Scheme.Modules.pullback f ≅ Scheme.Modules.pullback f ⋙ E'.inverse :=
    (Functor.Monoidal.commTensorRight N (F := Scheme.Modules.pullback f)).symm
  let e := AlgebraicGeometry.SheafCohomology.Projective.EquivalenceRightAdjointMate.inverseEquivalenceCommutesWithRightAdjoint E.symm E'.symm
    (Scheme.Modules.pullback f) (Scheme.Modules.pushforward f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) h
  exact (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalTensorObjIso ((Scheme.Modules.pushforward f).obj M) P).symm ≪≫
    e.app M ≪≫ (Scheme.Modules.pushforward f).mapIso (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalTensorObjIso M P')

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleProjectionFormula.Construction

import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GenericFieldTest
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare

/-! # Evaluation Generic Test -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationGenericTest.CM

noncomputable section

/-! The constructed evaluation field gives a canonical identification
of the actual TateComparison number-field test with the q-adic test used for
integral specialization. The underlying field-point map is the identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
  {q : ℕ} [Fact q.Prime] (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q)
  {L : Type} [Field L] [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L]

def originalBase : Spec (.of L) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Witt.ArithmeticBase.CM.Generic.F q) L)) ≫
    Spec.map (CommRingCat.ofHom ((Witt.ArithmeticBase.CM.Generic.padicToField q).comp (QadicModelMap.CM.localFieldEmbedding j)))

def testIso :
    (Over.map (Spec.map (CommRingCat.ofHom (QadicModelMap.CM.localFieldEmbedding j)))).obj
      (Over.mk (EvaluationBaseSquare.CM.fieldBase (L := L) (q := q))) ≅
    Over.mk (originalBase (L := L) j) :=
  GenericFieldTest.CM.testIso (QadicModelMap.CM.localFieldEmbedding j) (Witt.ArithmeticBase.CM.Generic.padicToField q) (algebraMap (Witt.ArithmeticBase.CM.Generic.F q) L)

theorem testIso_hom_left : (testIso (L := L) j).hom.left = 𝟙 (Spec (.of L)) :=
  GenericFieldTest.CM.testIso_hom_left (QadicModelMap.CM.localFieldEmbedding j) (Witt.ArithmeticBase.CM.Generic.padicToField q) (algebraMap (Witt.ArithmeticBase.CM.Generic.F q) L)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationGenericTest.CM

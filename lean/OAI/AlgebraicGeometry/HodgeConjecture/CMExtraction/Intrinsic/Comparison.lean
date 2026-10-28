import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Forms
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ComparisonAction

/-! # Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Comparison

noncomputable section

/-! The actual PEL Albanese supplies GeometricComparison's model. The active Hecke
realization is constructed by restricting TateComparison's original action, and its
Betti action is exactly the native CMExtraction active action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def nativeComparisonModel (hg : D.pel.HasIntegralModelGeometry)
    (hq : D.pel.IsGoodCompletelySplitPrime)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q) :
    NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q (HeckeCycles.QadicModelMap.CM.localFieldEmbedding j) :=
  HeckeCycles.AlbaneseModel.CM.comparisonModel D.pel hg j hq.2.2.2.1

theorem nativeComparisonModel_variety (hg : D.pel.HasIntegralModelGeometry)
    (hq : D.pel.IsGoodCompletelySplitPrime)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q) :
    (nativeComparisonModel D hg hq j).variety.scheme = D.pel.albaneseGroup.X := rfl

abbrev nativeActiveCommRing
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ]
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) : CommRing (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) := by
  exact { (inferInstance : Ring (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q)) with
    mul_comm := fun a b => e.injective (by
      have hm : e a * e b = e b * e a :=
        Subtype.ext (AbelianScheme.TateComparison.Commutativity.spherical_mul_comm s q hElementaryDivisors (e a).val (e b).val)
      exact (e.map_mul a b).trans (hm.trans (e.map_mul b a).symm)) }

theorem native_active_comparison_realization
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ]
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q) :
    letI := nativeActiveCommRing D e hElementaryDivisors
    ∃ R : (nativeComparisonModel D hg hq j).HeckeRealization (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q),
      R.action = (HeckeCycles.EndomorphismComparison.CM.rationalEquiv (nativeComparisonModel D hg hq j).variety.scheme).toAlgHom.comp
        (A.algebraAction.comp (RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e)) ∧
      (nativeComparisonModel D hg hq j).bettiHecke D.pel.complexEmbedding R =
        (fun h => (Forms.activeBettiAction D A e h : Module.End ℚ D.pel.H1)) := by
  let := nativeActiveCommRing D e hElementaryDivisors
  apply HeckeCycles.Intrinsic.ComparisonAction.CM.native_hecke_realization D.pel hg j hq.2.2.2.1
  intro h
  exact hA.cohomology _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Comparison

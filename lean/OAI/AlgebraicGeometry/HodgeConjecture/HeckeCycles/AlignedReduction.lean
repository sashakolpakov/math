import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseReductionMap
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionTargetIdentification

/-! # Aligned Reduction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlignedReduction.CM

noncomputable section

/-! Keep the original arithmetic reduction map and the specialization
comparison's target isomorphism in one constructed commuting square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseReductionMap.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionComparisonModel.CM

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator)
  (res : AbelianScheme.TateComparison.Data.modelRing K D.denominator →+* ZMod q)
  (hres : res.comp (algebraMap (NumberField.RingOfIntegers K)
    (AbelianScheme.TateComparison.Data.modelRing K D.denominator)) = j.residue)

local notation "red" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q)
local notation "t" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.integralBase j D.denominator hcop
local notation "br" => Spec.map (CommRingCat.ofHom res)
local notation "e" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM.comparisonIso D hg j hcop res hres

def sourceReduction : ReductionComparisonModel.CM.ReductionMap (AlbaneseModel.CM.arithmeticAlbanese D hg).2 (AlbaneseMapCompatibility.CM.arithmeticMap D hg) red t br :=
  ReductionTargetIdentification.CM.replaceTarget (AlbaneseModel.CM.arithmeticAlbanese D hg).2
    (AlbaneseMapCompatibility.CM.arithmeticMap D hg) red t br (AlbaneseReductionMap.CM.nativeReduction D hg j hcop res hres) e
    (AlbaneseReductionMap.CM.target_identification D hg j hcop res hres)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlignedReduction.CM

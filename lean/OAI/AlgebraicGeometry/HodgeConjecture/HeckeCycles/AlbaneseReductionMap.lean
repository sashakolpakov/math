import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionComparisonModel

/-! # Albanese Reduction Map -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseReductionMap.CM

noncomputable section

/-! Construct the reduction comparison for the actual arithmetic
Albanese source. Its target identification is precisely the one used
by the source-specialization endomorphism map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.SpecialFiber
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
local notation "wr" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.special_base_compatible j D.denominator hcop res hres

def nativeReduction : ReductionComparisonModel.CM.ReductionMap (AlbaneseModel.CM.arithmeticAlbanese D hg).2 (AlbaneseMapCompatibility.CM.arithmeticMap D hg) red t br :=
  ReductionComparisonModel.CM.reductionMap (AlbaneseModel.CM.arithmeticAlbanese D hg).2 (AlbaneseMapCompatibility.CM.arithmeticMap D hg) red t br wr

theorem target_identification :
    (nativeReduction D hg j hcop res hres).targetIso.hom =
      (AlbaneseModel.CM.SpecialFiber.albaneseSpecialFiberIso D hg j hcop res hres).hom :=
  (ReductionComparisonModel.CM.reductionMap_target_hom (AlbaneseModel.CM.arithmeticAlbanese D hg).2 (AlbaneseMapCompatibility.CM.arithmeticMap D hg) red t br wr).trans
    (AlbaneseMapCompatibility.CM.special_albanese_iso D hg j hcop res hres).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseReductionMap.CM

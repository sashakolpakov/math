import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel

/-! # Albanese Map Compatibility -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM

noncomputable section

/-! The integral Albanese map is constructed with its proved generic
comparison equation. Its generic map is identified with TateComparison, and its
special target is the original arithmetic Albanese fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.SpecialFiber

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

def arithmeticMap : D.model.space ⟶ (AlbaneseModel.CM.arithmeticAlbanese D hg).2.scheme := by
  let : IsIso D.componentAssembly := hg.decomposition
  exact D.components.totalMap (asIso D.componentAssembly) ≫
    (AbelianScheme.TateComparison.Products.componentProductComparison D.components.A).inv

theorem generic_arithmeticMap :
    (Over.pullback D.generic).map (arithmeticMap D hg) = D.albaneseMap hg := rfl

variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator)

local notation "A" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D hg j hcop
local notation "t" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.integralBase j D.denominator hcop
local notation "eta" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q])
local notation "jq" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.localFieldEmbedding j)
local notation "w" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.generic_base_compatible j D.denominator D.denominator_ne_zero hcop

def nativeSource : Source.ComparisonModel.CM.SourceMap A :=
  Source.ComparisonModel.CM.sourceMap (AlbaneseModel.CM.arithmeticAlbanese D hg).2
    (arithmeticMap D hg) D.generic t w

abbrev integralSource := (nativeSource D hg j hcop).integralSource
abbrev integralMap := (nativeSource D hg j hcop).integralMap
abbrev genericSource := (nativeSource D hg j hcop).genericSource
abbrev genericMap := (nativeSource D hg j hcop).genericMap
abbrev genericSourceIso := (nativeSource D hg j hcop).sourceIso

theorem genericMap_eq : CM.genericMap D hg j hcop = D.albaneseMap hg :=
  generic_arithmeticMap D hg

variable (res : AbelianScheme.TateComparison.Data.modelRing K D.denominator →+* ZMod q)
  (hres : res.comp (algebraMap (NumberField.RingOfIntegers K)
    (AbelianScheme.TateComparison.Data.modelRing K D.denominator)) = j.residue)

local notation "red" => OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q)
local notation "br" => Spec.map (CommRingCat.ofHom res)
local notation "wr" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.special_base_compatible j D.denominator hcop res hres

theorem special_albanese_iso :
    (AlbaneseModel.CM.SpecialFiber.albaneseSpecialFiberIso D hg j hcop res hres).hom =
      (BaseChangeSquare.CM.factorIso red t br wr (AlbaneseModel.CM.arithmeticAlbanese D hg).2.scheme).inv := by
  have he : AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso (AlbaneseModel.CM.arithmeticAlbanese D hg).2 red t br wr =
      BaseChangeSquare.CM.factorIso red t br wr (AlbaneseModel.CM.arithmeticAlbanese D hg).2.scheme :=
    Iso.ext (BaseChangeSquare.CM.groupFactor_hom red t br wr (AlbaneseModel.CM.arithmeticAlbanese D hg).2)
  exact congrArg Iso.inv he

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility.CM

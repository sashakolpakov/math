import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseProduct
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AbelianDimension
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare

/-! # Albanese Model -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM

/-! Construct GeometricComparison's abelian H¹ model from the exact total Albanese in
TateComparison, over the same arithmetic base and chosen ordinary prime. Smoothness,
properness, geometric connectedness, relative dimension, and the generic
identification are all derived from IntegralModel's component geometry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseProduct.CM

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

def arithmeticAlbanese : Σ g : ℕ,
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (AbelianScheme.TateComparison.Data.modelBase K D.denominator) := by
  let : IsDomain (AbelianScheme.TateComparison.Data.modelRing K D.denominator) := Localization.Away.isDomain
    (Nat.cast_ne_zero.mpr D.denominator_ne_zero)
  let G := (AbelianScheme.TateComparison.Products.componentProduct D.components.A).X
  have hG := AlbaneseProduct.CM.component_product_geometry D.components.A hg.abelianGeometry
  let : Smooth G.hom := hG.1
  let : IsProper G.hom := hG.2.1
  let : GeometricallyConnected G.hom := hG.2.2
  let b : AbelianScheme.TateComparison.Data.modelBase K D.denominator := D.generic (IsLocalRing.closedPoint K)
  exact ⟨ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimension.Construction.fiberDimension G b, AbelianDimension.CM.abelianScheme G b⟩

theorem arithmeticAlbanese_scheme :
    (arithmeticAlbanese D hg).2.scheme = (AbelianScheme.TateComparison.Products.componentProduct D.components.A).X := rfl

variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator)

/-- The exact number-field Albanese and its integral q-adic base change,
with the canonical group-preserving generic-fiber isomorphism. -/
def comparisonModel : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q (QadicModelMap.CM.localFieldEmbedding j) :=
  BaseChangeSquare.CM.ComparisonModel.model (arithmeticAlbanese D hg).2 D.generic
    (QadicModelMap.CM.integralBase j D.denominator hcop)
    (QadicModelMap.CM.generic_base_compatible j D.denominator D.denominator_ne_zero hcop)

theorem comparisonModel_variety :
    (comparisonModel D hg j hcop).variety.scheme = D.albaneseGroup.X := rfl

theorem comparisonModel_integral :
    (comparisonModel D hg j hcop).integral.scheme =
      (Over.pullback (QadicModelMap.CM.integralBase j D.denominator hcop)).obj
        (AbelianScheme.TateComparison.Products.componentProduct D.components.A).X := rfl

/-- CMPoints's chosen embeddings satisfy GeometricComparison's literal compatibility
condition for this model, without making a second choice of place. -/
theorem comparisonModel_place :
    (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp (QadicModelMap.CM.localFieldEmbedding j) =
      j.iota.comp j.fieldInClosure := j.closure_compatibility.symm

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.SpecialFiber

/-! Canonical identifications with the residue fiber used in CMPoints.
They follow from the proved equality of the actual specialization maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
  {q : ℕ} [Fact q.Prime] (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q)
  (d : ℕ) (hcop : Nat.Coprime q d) (residue : AbelianScheme.TateComparison.Data.modelRing K d →+* ZMod q)
  (hres : residue.comp (algebraMap (NumberField.RingOfIntegers K) (AbelianScheme.TateComparison.Data.modelRing K d)) = j.residue)

/-- Every scheme over the original arithmetic base has the same special
fiber whether reduced directly or first completed along the chosen prime. -/
def schemeSpecialFiberIso (X : Over (AbelianScheme.TateComparison.Data.modelBase K d)) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[q] →+* ZMod q)))).obj
      ((Over.pullback (QadicModelMap.CM.integralBase j d hcop)).obj X) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom residue))).obj X :=
  ((Over.pullbackComp
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[q] →+* ZMod q)))
    (QadicModelMap.CM.integralBase j d hcop)).app X).symm ≪≫
      eqToIso (congrArg (fun f => (Over.pullback f).obj X)
        (QadicModelMap.CM.special_base_compatible j d hcop residue hres))

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  {s : ℕ} (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (jD : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hden : Nat.Coprime q D.denominator)
  (res : AbelianScheme.TateComparison.Data.modelRing K D.denominator →+* ZMod q)
  (hresD : res.comp (algebraMap (NumberField.RingOfIntegers K)
    (AbelianScheme.TateComparison.Data.modelRing K D.denominator)) = jD.residue)

def albaneseSpecialFiberGroupIso :
    Grp.mk (comparisonModel D hg jD hden).specialFiber.scheme ≅
      Grp.mk (((arithmeticAlbanese D hg).2).pullback
        (Spec.map (CommRingCat.ofHom res))).scheme :=
  (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorGroupIso (arithmeticAlbanese D hg).2
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[q] →+* ZMod q)))
    (QadicModelMap.CM.integralBase jD D.denominator hden) (Spec.map (CommRingCat.ofHom res))
    (QadicModelMap.CM.special_base_compatible jD D.denominator hden res hresD)).symm

def albaneseSpecialFiberIso :
    (comparisonModel D hg jD hden).specialFiber.scheme ≅
      (AbelianScheme.TateComparison.BaseChange.baseChangedGroup (AbelianScheme.TateComparison.Products.componentProduct D.components.A).X
        (Spec.map (CommRingCat.ofHom res))).X :=
  (Grp.forget _).mapIso (albaneseSpecialFiberGroupIso D hg jD hden res hresD)

theorem albaneseSpecialFiberIso_group :
    letI : GrpObj (AbelianScheme.TateComparison.BaseChange.baseChangedGroup (AbelianScheme.TateComparison.Products.componentProduct D.components.A).X
      (Spec.map (CommRingCat.ofHom res))).X :=
        (AbelianScheme.TateComparison.BaseChange.baseChangedGroup (AbelianScheme.TateComparison.Products.componentProduct D.components.A).X
          (Spec.map (CommRingCat.ofHom res))).grp
    IsMonHom (albaneseSpecialFiberIso D hg jD hden res hresD).hom := by
  let : GrpObj (AbelianScheme.TateComparison.BaseChange.baseChangedGroup (AbelianScheme.TateComparison.Products.componentProduct D.components.A).X
    (Spec.map (CommRingCat.ofHom res))).X :=
      (AbelianScheme.TateComparison.BaseChange.baseChangedGroup (AbelianScheme.TateComparison.Products.componentProduct D.components.A).X
        (Spec.map (CommRingCat.ofHom res))).grp
  exact (albaneseSpecialFiberGroupIso D hg jD hden res hresD).hom.hom.isMonHom_hom

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.SpecialFiber

end

end OAI

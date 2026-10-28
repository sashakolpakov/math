import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Naturality
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Forms
import OAI.RepresentationTheory.Theta.Geometric.ComponentVarieties
import OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.Transport

/-! # Base -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base

noncomputable section

/-!
# Finiteness of the native Albanese Betti space

The relative projective embedding is base-changed to an actual smooth
projective presentation. The IntegralModel Betti isomorphism and the canonical
iterated-base-change isomorphisms then give finiteness of the precise
GeometricTheta Albanese H¹, with no finite-dimensionality hypothesis.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.RepresentationTheory.Theta.Geometric.ComponentVarieties
open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def singleBaseSpacePresentation (hg : D.pel.HasIntegralModelGeometry) :
    Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation where
  carrier := ((Over.pullback D.pel.complexPoint).obj D.pel.model.space).left
  structureMap := ((Over.pullback D.pel.complexPoint).obj D.pel.model.space).hom
  projective := RepresentationTheory.Theta.Geometric.ComponentVarieties.RelativeProjective.complexProjectivePresentation
    (Classical.choice hg.projective) D.pel.complexPoint
  smooth := by
    let : Smooth D.pel.model.space.hom := hg.smooth
    dsimp
    infer_instance

def singleBaseAlbaneseIso :
    (Over.pullback D.pel.complexPoint).obj D.pel.components.product ≅
      D.pel.complexAlbanese.X :=
  ((Over.pullback D.pel.complexPoint).mapIso
    (AbelianScheme.TateComparison.Products.componentProductComparison D.pel.components.A)).symm ≪≫
      (Over.pullbackComp D.pel.complexGenericPoint D.pel.generic).app
        (AbelianScheme.TateComparison.Products.componentProduct D.pel.components.A).X

theorem native_betti_finite (hg : D.pel.HasIntegralModelGeometry) :
    FiniteDimensional ℚ D.pel.H1 := by
  let : IsIso D.pel.componentAssembly := hg.decomposition
  let P := singleBaseSpacePresentation D hg
  let : FiniteDimensional ℚ
      (PELModuli.IntegralModel.Product.bettiQ ((Over.pullback D.pel.complexPoint).obj D.pel.model.space) 1) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.projective_cohomology_finite P 1
  let f := D.pel.components.totalComplexMap D.pel.complexPoint
    (asIso D.pel.componentAssembly)
  let e := singleBaseAlbaneseIso D
  let b := ((Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℚ ℚ) 1).mapIso e.op).toLinearEquiv
  let a := (PELModuli.IntegralModel.Product.bettiPullbackQ f 1).comp b.toLinearMap
  exact Module.Finite.of_injective a (hg.betti.1.comp b.injective)

/-- IntegralModel's actual Betti pullback, with its canonical product/base-change coordinates. -/
def nativeAlbaneseBettiEquiv (hg : D.pel.HasIntegralModelGeometry) :
    D.pel.H1 ≃ₗ[ℚ] (singleBaseSpacePresentation D hg).rationalCohomology 1 := by
  let : IsIso D.pel.componentAssembly := hg.decomposition
  let b := ((Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℚ ℚ) 1).mapIso
    (singleBaseAlbaneseIso D).op).toLinearEquiv
  exact b.trans (LinearEquiv.ofBijective
    (PELModuli.IntegralModel.Product.bettiPullbackQ (D.pel.components.totalComplexMap D.pel.complexPoint
      (asIso D.pel.componentAssembly)) 1) hg.betti)

def singleBaseSpaceIso (hg : D.pel.HasIntegralModelGeometry) :
    (singleBaseSpacePresentation D hg).toOver ≅ D.pel.complexSpace :=
  (Over.pullbackComp D.pel.complexGenericPoint D.pel.generic).app D.pel.model.space

theorem singleBaseAlbaneseMap_compatibility (hg : D.pel.HasIntegralModelGeometry) :
    letI := hg.decomposition
    D.pel.components.totalComplexMap D.pel.complexPoint (asIso D.pel.componentAssembly) ≫
        (singleBaseAlbaneseIso D).hom =
      (singleBaseSpaceIso D hg).hom ≫ D.pel.complexAlbaneseMap hg := by
  let : IsIso D.pel.componentAssembly := hg.decomposition
  let t := D.pel.components.totalMap (asIso D.pel.componentAssembly)
  let a := (AbelianScheme.TateComparison.Products.componentProductComparison D.pel.components.A).inv
  change (Over.pullback D.pel.complexPoint).map t ≫
      ((Over.pullback D.pel.complexPoint).map a ≫
        (Over.pullbackComp D.pel.complexGenericPoint D.pel.generic).hom.app _) = _
  rw [← Category.assoc, ← Functor.map_comp]
  exact (Over.pullbackComp D.pel.complexGenericPoint D.pel.generic).hom.naturality (t ≫ a)

theorem nativeAlbaneseBettiEquiv_eq_pullback (hg : D.pel.HasIntegralModelGeometry) :
    (nativeAlbaneseBettiEquiv D hg).toLinearMap =
      PELModuli.IntegralModel.Product.bettiPullbackQ
        ((singleBaseSpaceIso D hg).hom ≫ D.pel.complexAlbaneseMap hg) 1 := by
  let : IsIso D.pel.componentAssembly := hg.decomposition
  change (PELModuli.IntegralModel.Product.bettiPullbackQ
    (D.pel.components.totalComplexMap D.pel.complexPoint (asIso D.pel.componentAssembly)) 1).comp
      (PELModuli.IntegralModel.Product.bettiPullbackQ (singleBaseAlbaneseIso D).hom 1) = _
  rw [← PELModuli.IntegralModel.Product.bettiPullbackQ_comp, singleBaseAlbaneseMap_compatibility D hg]
  rfl

/-- The Hodge realization obtained through the actual Albanese Betti isomorphism. -/
def nativeH1 (hHodgeDecomposition : Mem.HodgeDecompositionInput) (hg : D.pel.HasIntegralModelGeometry) :
    ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure D.pel.H1 :=
  (Mem.canonicalH1 hHodgeDecomposition (singleBaseSpacePresentation D hg)).transport
    (nativeAlbaneseBettiEquiv D hg).symm

theorem nativeAlbaneseBettiEquiv_isHodgeMap
    (hHodgeDecomposition : Mem.HodgeDecompositionInput) (hg : D.pel.HasIntegralModelGeometry) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (nativeH1 D hHodgeDecomposition hg)
      (Mem.canonicalH1 hHodgeDecomposition (singleBaseSpacePresentation D hg))
      (nativeAlbaneseBettiEquiv D hg).toLinearMap :=
  ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure.transport_symm_isHodgeMap _ _

theorem native_componentRestriction_isHodgeMap
    (hHodgeDecomposition : Mem.HodgeDecompositionInput) (hg : D.pel.HasIntegralModelGeometry)
    (j : Fin D.pel.componentCount) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (nativeH1 D hHodgeDecomposition hg)
      (Mem.canonicalH1 hHodgeDecomposition (D.componentVariety hg j).presentation)
      (Forms.componentRestriction D hg j) := by
  let f : (D.componentVariety hg j).toOver ⟶ (singleBaseSpacePresentation D hg).toOver :=
    D.componentComplexInclusion j ≫ (singleBaseSpaceIso D hg).inv
  have h := (Naturality.canonicalH1_pullback hHodgeDecomposition (D.componentVariety hg j).presentation
    (singleBaseSpacePresentation D hg) f).comp (nativeAlbaneseBettiEquiv_isHodgeMap D hHodgeDecomposition hg)
  have he : (PELModuli.IntegralModel.Product.bettiPullbackQ f 1).comp (nativeAlbaneseBettiEquiv D hg).toLinearMap =
      Forms.componentRestriction D hg j := by
    rw [nativeAlbaneseBettiEquiv_eq_pullback, ← PELModuli.IntegralModel.Product.bettiPullbackQ_comp]
    unfold Forms.componentRestriction
    congr 1
    exact (Category.assoc _ _ _).trans
      (congrArg (fun g => D.componentComplexInclusion j ≫ g)
        ((singleBaseSpaceIso D hg).inv_hom_id_assoc (D.pel.complexAlbaneseMap hg)))
  exact he ▸ h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base

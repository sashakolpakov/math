import OAI.AlgebraicGeometry.Comparison.Betti.Godement.CechImage
import OAI.AlgebraicGeometry.Comparison.Betti.IntegerImageQuasiIso
import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueDerived
import OAI.AlgebraicGeometry.Comparison.Betti.DerivedQuasiIsoSquare
import OAI.AlgebraicGeometry.Comparison.Betti.ImageExtensionSquare
import OAI.AlgebraicGeometry.Comparison.Betti.ImageAdjointNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Hypercohomology

/-! # Concrete Derived -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.ConcreteDerived.Godement

noncomputable section

/-! A proved comparison on finite acyclic Čech covers gives bijectivity of the actual normalized derived coefficient map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

local instance cechActualDerivedCategory (Z : TopCat.{0}) : HasDerivedCategory.{1} (ConstantSheafSections.ComplexSheaves Z) :=
  HasDerivedCategory.standard _

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} [Finite ι] (U : ι → Opens X)
  (K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ)
  (L : CochainComplex (ConstantSheafSections.ComplexSheaves Y) ℕ)
  (α : K ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj L)

theorem cech_directImageCohomologyMap_bijective
    (hU : iSup U = ⊤) (hV : (⨆ i, (Opens.map f).obj (U i)) = ⊤)
    (hK : ∀ q, SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := X) U
      ((Complex.SheafForget.Flasque.sheafForget X).obj (K.X q)))
    (hL : ∀ q, SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := Y) (fun i => (Opens.map f).obj (U i))
      ((Complex.SheafForget.Flasque.sheafForget Y).obj (L.X q)))
    (hα : QuasiIso (Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap f U (Godement.AdditiveImage.additiveDirectImageComplexMap f α))) (n : ℤ) :
    Function.Bijective (FlasqueDerived.directImageCohomologyMap f (K.extend (ComplexShape.embeddingUpIntGE 0))
      (L.extend (ComplexShape.embeddingUpIntGE 0)) (ImageExtensionSquare.extendDirectImageComplexMap f α) n) := by
  let γ := Godement.PushforwardBicomplex.godementDirectImageTotalMap f α
  let γI := ImageExtensionSquare.extendDirectImageComplexMap f γ
  let e := Godement.Hypercohomology.godementTotalAugmentationInt K
  let d := Godement.Hypercohomology.godementTotalAugmentationInt L
  have hn : QuasiIso (ImageExtensionSquare.natTopSectionsPullback f γ) :=
    Godement.CechImage.godementDirectImageTotalMap_global_quasiIso f U α hU hV hK hL hα
  have hi : QuasiIso (ImageAdjointNaturality.integerTopGlobalSectionsPullback f γI) :=
    IntegerImageQuasiIso.integerTopGlobalSectionsPullback_extend_quasiIso f γ hn
  have hbK : (Godement.Hypercohomology.godementTotalComplexInt K).IsStrictlyGE 0 := Godement.Hypercohomology.godementTotalComplexInt_nonnegative K
  have hbL : (Godement.Hypercohomology.godementTotalComplexInt L).IsStrictlyGE 0 := Godement.Hypercohomology.godementTotalComplexInt_nonnegative L
  have hγ : Function.Bijective (FlasqueDerived.directImageCohomologyMap f (Godement.Hypercohomology.godementTotalComplexInt K)
      (Godement.Hypercohomology.godementTotalComplexInt L) γI n) :=
    @FlasqueDerived.directImageCohomologyMap_bijective_of_flasque X Y f (Godement.Hypercohomology.godementTotalComplexInt K)
      (Godement.Hypercohomology.godementTotalComplexInt L) γI n 0 0 hbK hbL
      (FlasqueNatQuasiIso.extend_flasque _ (Godement.TotalFlasque.godementTotal_isFlasque K))
      (FlasqueNatQuasiIso.extend_flasque _ (Godement.TotalFlasque.godementTotal_isFlasque L)) hi
  have hs := ImageExtensionSquare.extendDirectImageComplexMap_square f α γ (Godement.Bicomplex.godementTotalAugmentation K)
    (Godement.Bicomplex.godementTotalAugmentation L) (Godement.PushforwardBicomplex.godementDirectImageTotalMap_augmentation f α)
  have ha := ImageAdjointNaturality.directImageAdjointComplexMap_square f (ImageExtensionSquare.extendDirectImageComplexMap f α) γI e d hs
  exact DerivedQuasiIsoSquare.Ext.coefficientDerivedMap_bijective_of_quasiIso_square (TopologicalSheafPullback.sheafInverseImage f)
    (ConstantSheafSections.standardConstantSheaf X) (ConstantSheafSections.standardConstantSheaf Y) (TopologicalSheafPullback.constantPullbackIso f).inv
    (ImageAdjointNaturality.directImageAdjointComplexMap f (ImageExtensionSquare.extendDirectImageComplexMap f α)) (ImageAdjointNaturality.directImageAdjointComplexMap f γI)
    e d ha (Godement.Hypercohomology.godementTotalAugmentationInt_quasiIso K) (Godement.Hypercohomology.godementTotalAugmentationInt_quasiIso L) n hγ

end

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.ConcreteDerived.Godement

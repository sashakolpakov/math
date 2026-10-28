import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PuncturedGenericPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.DeformationFlat
import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.PrimeNaturality

/-! # Laurent Naturality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.LaurentNaturality.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual support quotient maps on punctured Laurent charts -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

theorem affinePuncturedDeformation_support {R : Type} [CommRing R] (I P : Ideal R) :
    Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap (I.map (Ideal.Quotient.mk P)) ≫ Deformation.ClosedSupport.BundleCycles.closedSupportDeformationInclusion I P =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ (Ideal.Quotient.mk P))) ≫
        Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap I := by
  let q : CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra I) ⟶
      CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.map (Ideal.Quotient.mk P))) :=
    CommRingCat.ofHom (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationRingMap I P)
  let a : CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra I) ⟶ CommRingCat.of (LaurentPolynomial R) :=
    CommRingCat.ofHom (algebraMap (Deformation.Iff.BundleCycles.deformationAlgebra I) (LaurentPolynomial R))
  let b : CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.map (Ideal.Quotient.mk P))) ⟶
      CommRingCat.of (LaurentPolynomial (R ⧸ P)) :=
    CommRingCat.ofHom (algebraMap (Deformation.Iff.BundleCycles.deformationAlgebra (I.map (Ideal.Quotient.mk P))) (LaurentPolynomial (R ⧸ P)))
  let l : CommRingCat.of (LaurentPolynomial R) ⟶ CommRingCat.of (LaurentPolynomial (R ⧸ P)) :=
    CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ (Ideal.Quotient.mk P))
  have h : q ≫ b = a ≫ l := rfl
  exact (Spec.map_comp q b).symm.trans ((congrArg Spec.map h).trans (Spec.map_comp a l))

variable {X : Scheme.{0}} (I P : X.IdealSheafData) (U : X.AffineZariskiSite)

def supportLaurentQuotientMap :
    Spec (CommRingCat.of (LaurentPolynomial ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))) ⟶
      Spec (CommRingCat.of (LaurentPolynomial Γ(X, U.1))) :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ (Ideal.Quotient.mk (P.ideal U))))

theorem supportLaurentChart_toAmbient :
    LaurentChart.BundleCycles.supportLaurentChart I P U ≫ Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P =
      supportLaurentQuotientMap P U ≫ Global.PuncturedLaurentChart.BundleCycles.globalPuncturedLaurentChart I U := by
  let l : Spec (CommRingCat.of (LaurentPolynomial ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))) ⟶
      (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U := Affine.PuncturedDeformation.BundleCycles.affinePuncturedDeformationMap (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)
  exact (Category.assoc l ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U) (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P)).trans
    ((congrArg (fun k => l ≫ k) (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap_on_chart I P U)).trans
      ((Category.assoc l (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationInclusion (I.ideal U) (P.ideal U))
        ((Global.Deformation.BundleCycles.globalDeformationCover I).f U)).symm.trans
        ((congrArg (fun k => k ≫ (Global.Deformation.BundleCycles.globalDeformationCover I).f U)
          (affinePuncturedDeformation_support (I.ideal U) (P.ideal U))).trans (Category.assoc _ _ _))))

theorem supportPuncturedLaurentChart_toAmbient :
    LaurentChart.BundleCycles.supportPuncturedLaurentChart I P U ≫ LaurentChart.BundleCycles.supportPuncturedMap I P =
      supportLaurentQuotientMap P U ≫ Punctured.DeformationCharts.BundleCycles.puncturedLaurentChart I U := by
  apply (cancel_mono (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I)).mp
  rw [Category.assoc, LaurentChart.BundleCycles.supportPuncturedMap_inclusion, ← Category.assoc,
    LaurentChart.BundleCycles.supportPuncturedLaurentChart_inclusion, supportLaurentChart_toAmbient,
    Category.assoc, Punctured.DeformationCharts.BundleCycles.puncturedLaurentChart_inclusion]

theorem supportCoefficientChart_toAmbient :
    Projection.BundleCycles.supportCoefficientChart P U ≫ P.subschemeι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (P.ideal U))) ≫ U.2.fromSpec := by
  exact (P.subschemeCover_map_subschemeι U).trans
    ((Category.assoc _ _ _).trans (congrArg (fun k =>
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (P.ideal U))) ≫ k) U.2.isoSpec_inv_ι))

omit U in
theorem supportPuncturedGenericPoint_toAmbient (x : P.subscheme) :
    LaurentChart.BundleCycles.supportPuncturedMap I P (PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint I P x) =
      Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint I (P.subschemeι x) := by
  obtain ⟨U, p, hp⟩ := P.subschemeCover.openCover.exists_eq x
  have hpoint : P.subschemeι (Projection.BundleCycles.supportCoefficientChart P U p) =
      U.2.fromSpec (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (P.ideal U))) p) :=
    congrArg (fun k => k p) (supportCoefficientChart_toAmbient P U)
  have hs := PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint_on_chart I P U p
  have hq := Laurent.PrimeNaturality.BundleCycles.laurentPrimePoint_map (Ideal.Quotient.mk (P.ideal U)) p
  have hc := congrArg (fun k => k (Laurent.FiberGenericPoint.BundleCycles.laurentPrimePoint ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) p))
    (supportPuncturedLaurentChart_toAmbient I P U)
  exact (congrArg (fun z => LaurentChart.BundleCycles.supportPuncturedMap I P (PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint I P z)) hp.symm).trans
    ((congrArg (LaurentChart.BundleCycles.supportPuncturedMap I P) hs).trans
      (hc.trans ((congrArg (Punctured.DeformationCharts.BundleCycles.puncturedLaurentChart I U) hq).trans
        ((Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint_on_chart I U _).symm.trans
          (congrArg (Punctured.DeformationFlat.BundleCycles.puncturedFiberGenericPoint I) (hpoint.symm.trans (congrArg P.subschemeι hp)))))))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.LaurentNaturality.BundleCycles

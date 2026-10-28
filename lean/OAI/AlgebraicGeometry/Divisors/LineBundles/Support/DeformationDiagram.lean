import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.CoefficientDiagram
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Localization

/-! # Deformation Diagram -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.DeformationDiagram.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the extended-Rees diagram of a closed support

On each affine open the construction is literally the deformation algebra
over the quotient by the support ideal. Coefficient quotient maps define
the natural morphism from the ambient deformation diagram.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} (I P : X.IdealSheafData)

/-- Actual extended-Rees algebras over the support's quotient coefficient rings. -/
def supportDeformationDiagram : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U := CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U.unop))
  map {U V} f := CommRingCat.ofHom
    (Deformation.Maps.BundleCycles.deformationMap (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U.unop) (CoefficientDiagram.BundleCycles.supportCenterIdeal P I V.unop)
      ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map f).hom (CoefficientDiagram.BundleCycles.supportCenterIdeal_le_comap P I f))
  map_id U := by
    apply CommRingCat.hom_ext
    ext p n
    have h : ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map (𝟙 U)).hom =
        RingHom.id ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj U) :=
      congrArg CommRingCat.Hom.hom ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map_id U)
    change (AddMonoidAlgebra.mapRingHom ℤ
      ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map (𝟙 U)).hom p.val).coeff n = p.val.coeff n
    exact (AddMonoidAlgebra.coeff_mapRingHom
      ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map (𝟙 U)).hom p.val n).trans (DFunLike.congr_fun h _)
  map_comp {U V W} f g := by
    apply CommRingCat.hom_ext
    ext p n
    have h : ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map (f ≫ g)).hom =
        ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map g).hom.comp ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map f).hom :=
      congrArg CommRingCat.Hom.hom ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map_comp f g)
    change (AddMonoidAlgebra.mapRingHom ℤ
      ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map (f ≫ g)).hom p.val).coeff n =
      (AddMonoidAlgebra.mapRingHom ℤ ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map g).hom
        (AddMonoidAlgebra.mapRingHom ℤ ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map f).hom p.val)).coeff n
    simp only [AddMonoidAlgebra.coeff_mapRingHom]
    exact DFunLike.congr_fun h _

/-- Coefficient quotients induce the actual natural maps of deformation algebras. -/
def deformationToSupportDiagram : Global.Deformation.BundleCycles.deformationDiagram I ⟶ supportDeformationDiagram I P where
  app U := CommRingCat.ofHom (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationRingMap (I.ideal U.unop) (P.ideal U.unop))
  naturality {U V} f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    apply Subtype.ext
    ext n
    let qU := Ideal.Quotient.mk (P.ideal U.unop)
    let qV := Ideal.Quotient.mk (P.ideal V.unop)
    let fR := (X.presheaf.map ((toOpensFunctor X).op.map f)).hom
    let fQ := ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map f).hom
    exact (AddMonoidAlgebra.coeff_mapRingHom qV (AddMonoidAlgebra.mapRingHom ℤ fR p.val) n).trans
      ((congrArg qV (AddMonoidAlgebra.coeff_mapRingHom fR p.val n)).trans
      ((AddMonoidAlgebra.coeff_mapRingHom fQ (AddMonoidAlgebra.mapRingHom ℤ qU p.val) n).trans
        (congrArg fQ (AddMonoidAlgebra.coeff_mapRingHom qU p.val n))).symm)

theorem deformationToSupportDiagram_surjective (U : X.AffineZariskiSite) :
    Function.Surjective ((deformationToSupportDiagram I P).app (.op U)) :=
  Deformation.ClosedSupport.BundleCycles.closedSupportDeformationRingMap_surjective (I.ideal U) (P.ideal U)

/-- Constants from the ambient scheme give the closed-support deformation's base map. -/
def supportDeformationDiagramMap : (toOpensFunctor X).op ⋙ X.presheaf ⟶ supportDeformationDiagram I P :=
  Global.Deformation.BundleCycles.deformationDiagramMap I ≫ deformationToSupportDiagram I P

theorem supportDeformationDiagramMap_apply (U : X.AffineZariskiSite) (r : Γ(X, U.1)) :
    (supportDeformationDiagramMap I P).app (.op U) r =
      algebraMap ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))
        (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)) (Ideal.Quotient.mk (P.ideal U) r) :=
  Deformation.Maps.BundleCycles.deformationMap_algebraMap (I.ideal U) (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)
    (Ideal.Quotient.mk (P.ideal U)) (fun _ hr => Ideal.mem_map_of_mem _ hr) r

/-- The actual closed-support deformation rings commute with affine base localization. -/
theorem supportDeformationDiagramMap_coequifibered :
    (supportDeformationDiagramMap I P).Coequifibered := by
  apply coequifibered_iff_forall_isLocalizationAway.mpr
  intro U r
  let V : X.AffineZariskiSite := U.basicOpen r
  let a : (.op U : X.AffineZariskiSiteᵒᵖ) ⟶ .op V :=
    (homOfLE (U.basicOpen_le r)).op
  let A : CommRingCat := (CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)
  let B : CommRingCat := (CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op V)
  let f : A ⟶ B := (CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map a
  let : Algebra A B := f.hom.toAlgebra
  have : IsLocalization.Away ((CoefficientDiagram.BundleCycles.supportCoefficientMap P).app (.op U) r) B :=
    coequifibered_iff_forall_isLocalizationAway.mp (CoefficientDiagram.BundleCycles.supportCoefficientMap_coequifibered P) U r
  have hI : (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U).map (algebraMap A B) = CoefficientDiagram.BundleCycles.supportCenterIdeal P I V :=
    CoefficientDiagram.BundleCycles.supportCenterIdeal_map P I a
  have hle : CoefficientDiagram.BundleCycles.supportCenterIdeal P I U ≤ (CoefficientDiagram.BundleCycles.supportCenterIdeal P I V).comap (algebraMap A B) :=
    CoefficientDiagram.BundleCycles.supportCenterIdeal_le_comap P I a
  have h := Deformation.Localization.BundleCycles.deformationMap_isLocalization (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)
    (Submonoid.powers ((CoefficientDiagram.BundleCycles.supportCoefficientMap P).app (.op U) r)) B
    (CoefficientDiagram.BundleCycles.supportCenterIdeal P I V) hI hle
  let : Algebra (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U))
      (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I V)) :=
    (Deformation.Maps.BundleCycles.deformationMap (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U) (CoefficientDiagram.BundleCycles.supportCenterIdeal P I V) f.hom hle).toAlgebra
  let : Algebra ((supportDeformationDiagram I P).obj (.op U))
      (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I V)) :=
    (Deformation.Maps.BundleCycles.deformationMap (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U) (CoefficientDiagram.BundleCycles.supportCenterIdeal P I V) f.hom hle).toAlgebra
  change IsLocalization.Away ((supportDeformationDiagramMap I P).app (.op U) r)
    (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I V))
  rw [supportDeformationDiagramMap_apply I P U r]
  simp only [Deformation.Localization.BundleCycles.deformationDenominators, Submonoid.map_powers] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.DeformationDiagram.BundleCycles

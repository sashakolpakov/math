import OAI.NumberTheory.PadicHodge.IntegralComparison.FirstThreeCechReduction
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OrdinaryReduction
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SmallReductionSquare

/-! # Padic One -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.PadicOne.IntrinsicH

/-! The genuine H¹ projection from the full ordinary Čech complex to
the accepted first-three-form comparison commutes with reduction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex ℤ_[p] X
local notation "E" => FormalCoproduct.cech (FormalCoproduct.mk
  (GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X) U)
local notation "K" => HomologicalComplex₂.total
  (OrdinaryCechUnit.IntrinsicOrdinary.bicomplex p X) (ComplexShape.up ℕ)
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U

local instance cech_additive : (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor ℤ_[p] X U).Additive := by
  change (FormalCoproduct.cochainComplexFunctor E).Additive
  infer_instance

def projection : K ⟶ C :=
  GeometricComparison.FirstThree.MappedTotalOne.FirstThreeMappedTotalHOne.map ℤ_[p] (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor ℤ_[p] X U) P

omit [X.left.IsSeparated] in
theorem quasiIsoAt : QuasiIsoAt (projection p X) 1 :=
  GeometricComparison.FirstThree.MappedTotalOne.FirstThreeMappedTotalHOne.quasiIsoAt ℤ_[p] (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor ℤ_[p] X U) P

def cohomologyIso : (K).homology 1 ≅ (C).homology 1 := by
  let := quasiIsoAt p X
  exact isoOfQuasiIsoAt (projection p X) 1

def globalEquiv : (K).homology 1 ≃ₗ[ℤ_[p]] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1 :=
  (cohomologyIso p X).toLinearEquiv.trans (GeometricComparison.IntrinsicPadic.IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates.equiv p X).symm

omit [X.left.IsSeparated] in
theorem global_coordinates (x : (K).homology 1) :
    GeometricComparison.IntrinsicPadic.IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates.equiv p X (globalEquiv p X x) =
      (cohomologyIso p X).hom x :=
  (GeometricComparison.IntrinsicPadic.IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates.equiv p X).apply_symm_apply _

omit [X.left.IsSeparated] in
theorem projection_reduction (n : ℕ) :
    projection p X ≫ GeometricComparison.CechPresheaf.QuotientProjection.CechPresheafQuotientProjection.map ℤ_[p]
        ((Ideal.span {(p : ℤ_[p])}) ^ (n+1)) E (GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex P) =
      OrdinaryReduction.IntrinsicOrdinary.map p X n ≫
        GeometricComparison.IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.projection ℤ_[p] X U
          ((Ideal.span {(p : ℤ_[p])}) ^ (n+1)) :=
  FirstThreeCechReduction.natural ℤ_[p] ((Ideal.span {(p : ℤ_[p])}) ^ (n+1)) E P

omit [X.left.IsSeparated] in
theorem truncated_reduction (n : ℕ) :
    GeometricComparison.PrincipalCochainExact.PrincipalCochainQuotient.projection ℤ_[p] C (p : ℤ_[p]) (n+1) ≫
      (GeometricComparison.IntegralCech.QuotientTotal.IntegralCechQuotientTotal.iso ℤ_[p] X U ((Ideal.span {(p : ℤ_[p])}) ^ (n+1))).hom =
    GeometricComparison.CechPresheaf.QuotientProjection.CechPresheafQuotientProjection.map ℤ_[p] ((Ideal.span {(p : ℤ_[p])}) ^ (n+1))
      E (GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex P) :=
  GeometricComparison.CechPresheaf.QuotientProjection.CechPresheafQuotientProjection.total ℤ_[p] ((Ideal.span {(p : ℤ_[p])}) ^ (n+1))
    E (GeometricComparison.IntegralCech.QuotientTotal.IntegralCechQuotientTotal.finiteIndices ℤ_[p] X U) (GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex P)

end NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.PadicOne.IntrinsicH

namespace NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.PadicOne.IntrinsicHReduction

/-! Full ordinary reduction and the accepted first-three quotient have
the same H¹ coordinates, through their literal projection maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem cancel_iso {A : Type*} [Category A] {V W T D : A}
    (p : V ⟶ W) (b : W ⟶ T) (t : T ≅ D) (a : V ⟶ D)
    (h : p ≫ b ≫ t.hom = a) : p ≫ b = a ≫ t.inv := by
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem mapped_cancel_iso {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {V W T D Q : A} (p : V ⟶ W) (b : W ⟶ T)
    (t : T ≅ D) (a : V ⟶ Q) (q : Q ⟶ D)
    (h : p ≫ b ≫ t.hom = a ≫ q) :
    F.map p ≫ F.map b = F.map a ≫ F.map q ≫ (F.mapIso t).inv := by
  have hh : F.map p ≫ F.map b ≫ (F.mapIso t).hom = F.map a ≫ F.map q := by
    simpa only [Functor.map_comp, Functor.mapIso_hom] using congrArg F.map h
  exact (cancel_iso (F.map p) (F.map b) (F.mapIso t) (F.map a ≫ F.map q) hh).trans
    (Category.assoc _ _ _)

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "K" => HomologicalComplex₂.total
  (OrdinaryCechUnit.IntrinsicOrdinary.bicomplex p X) (ComplexShape.up ℕ)
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U
local notation "H" => HomologicalComplex.homologyFunctor (ModuleCat ℤ_[p]) (ComplexShape.up ℕ) 1

omit [X.left.IsSeparated] in
theorem homology_square (n : ℕ) :
    HomologicalComplex.homologyMap (IntrinsicH.projection p X) 1 ≫
      HomologicalComplex.homologyMap
        (GeometricComparison.PrincipalCochainExact.PrincipalCochainQuotient.projection ℤ_[p] C (p : ℤ_[p]) (n+1)) 1 =
    HomologicalComplex.homologyMap (OrdinaryReduction.IntrinsicOrdinary.map p X n) 1 ≫
      HomologicalComplex.homologyMap
        (GeometricComparison.IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.projection ℤ_[p] X U
          ((Ideal.span {(p : ℤ_[p])}) ^ (n+1))) 1 ≫
      (GeometricComparison.IntegralCech.QuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X U
        ((Ideal.span {(p : ℤ_[p])}) ^ (n+1)) 1).inv := by
  have h := IntrinsicH.projection_reduction p X n
  rw [← IntrinsicH.truncated_reduction] at h
  exact mapped_cancel_iso
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ_[p]) (.up ℕ) 1)
    (IntrinsicH.projection p X)
    (GeometricComparison.PrincipalCochainExact.PrincipalCochainQuotient.projection ℤ_[p] C (p : ℤ_[p]) (n+1))
    (GeometricComparison.IntegralCech.QuotientTotal.IntegralCechQuotientTotal.iso ℤ_[p] X U ((Ideal.span {(p : ℤ_[p])}) ^ (n+1)))
    (OrdinaryReduction.IntrinsicOrdinary.map p X n)
    (GeometricComparison.IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.projection ℤ_[p] X U
      ((Ideal.span {(p : ℤ_[p])}) ^ (n+1))) h

theorem coordinates (n : ℕ) (x : (K).homology 1) :
    (GeometricComparison.IntrinsicPadic.FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).hom
        (HomologicalComplex.homologyMap (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X n).inv 1
          (OrdinaryReduction.IntrinsicOrdinary.reduction p X n 1 x)) =
    GeometricComparison.CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p] C (p : ℤ_[p]) (n+1) 1
      ((IntrinsicH.cohomologyIso p X).hom x) := by
  have h := ConcreteCategory.congr_hom (homology_square p X n) x
  let e := HomologicalComplex.homologyMapIso (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X n) 1
  change (GeometricComparison.IntegralCech.QuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X U
      ((Ideal.span {(p : ℤ_[p])}) ^ (n+1)) 1).inv
      (HomologicalComplex.homologyMap
        (GeometricComparison.IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.projection ℤ_[p] X U
          ((Ideal.span {(p : ℤ_[p])}) ^ (n+1))) 1
        (e.hom (e.inv (OrdinaryReduction.IntrinsicOrdinary.reduction p X n 1 x)))) = _
  exact (congrArg
    (fun z => (GeometricComparison.IntegralCech.QuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X U
      ((Ideal.span {(p : ℤ_[p])}) ^ (n+1)) 1).inv
      (HomologicalComplex.homologyMap
        (GeometricComparison.IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.projection ℤ_[p] X U
          ((Ideal.span {(p : ℤ_[p])}) ^ (n+1))) 1 z))
    (ConcreteCategory.congr_hom e.inv_hom_id
      (OrdinaryReduction.IntrinsicOrdinary.reduction p X n 1 x))).trans h.symm

end NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.PadicOne.IntrinsicHReduction

end

end OAI

import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticProductPoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointTransportDetection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductFactorBaseChange

/-! # Arithmetic Point Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticPointTransport.CM

noncomputable section

/-! The arithmetic-product point equivalence carries each actual
geometric component Albanese map to its prime-field point map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductBaseChange.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductPoints.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TransportedGeometricPoints.CM

variable (q : ℕ) [Fact q.Prime] {S : Scheme} {r : ℕ}
  (A : Fin r → CommGrp (Over S)) (b : Spec (.of (ZMod q)) ⟶ S)
  (d : Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)) ⟶ S) (hd : TransportedGeometricPoints.CM.geometricScalarBase q ≫ b = d)

local notation "SP" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM.changedGroup (OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Products.componentProduct A) b
local notation "GP" => OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Products.componentProduct (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductBaseChange.CM.changedFactors A d)
local notation "cmp" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticProductPoints.CM.comparison A b (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TransportedGeometricPoints.CM.geometricScalarBase q) d hd
local notation "cmpG" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticProductPoints.CM.comparisonGroup A b (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TransportedGeometricPoints.CM.geometricScalarBase q) d hd

local instance : GrpObj (GP).X := (GP).grp
local instance : IsCommMonObj (GP).X := (GP).comm
local instance : GrpObj (SP).X := (SP).grp
local instance : IsCommMonObj (SP).X := (SP).comm

def pointsIso : Additive (Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) ⟶ (GP).X) ≃+
    Additive (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ (SP).X) :=
  @PointTransportDetection.CM.TransportedAddEquiv.pointAddEquiv q _ SP GP cmp (cmpG).hom.hom.isMonHom_hom

theorem product_point (p : Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) ⟶ (GroupBaseChange.CM.changedGroup (AbelianScheme.TateComparison.Products.componentProduct A) d).X) :
    pointsIso q A b d hd (Additive.ofMul (p ≫ (ProductBaseChange.CM.productBaseChangeIso A d).hom)) =
      Additive.ofMul (PrimeFieldPoints.CM.pointEquiv b (TransportedGeometricPoints.CM.geometricScalarBase q) d hd
        (AbelianScheme.TateComparison.Products.componentProduct A).X p) := by
  apply Additive.toMul.injective
  exact (TransportedGeometricPoints.CM.pointEquiv_apply q SP GP cmp (p ≫ (ProductBaseChange.CM.productBaseChangeIso A d).hom)).trans
    (ArithmeticProductPoints.CM.product_point A b (TransportedGeometricPoints.CM.geometricScalarBase q) d hd p)

theorem map_point {X : Over S} (a : X ⟶ (AbelianScheme.TateComparison.Products.componentProduct A).X)
    (p : Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) ⟶ (Over.pullback d).obj X) :
    pointsIso q A b d hd
      (Additive.ofMul ((p ≫ (Over.pullback d).map a) ≫ (ProductBaseChange.CM.productBaseChangeIso A d).hom)) =
        Additive.ofMul (PrimeFieldPoints.CM.pointEquiv b (TransportedGeometricPoints.CM.geometricScalarBase q) d hd X p ≫
          (Over.pullback b).map a) :=
  (product_point q A b d hd (p ≫ (Over.pullback d).map a)).trans
    (congrArg Additive.ofMul (PrimeFieldPoints.CM.pointEquiv_map b (TransportedGeometricPoints.CM.geometricScalarBase q) d hd a p))

theorem component_point {X : Over S} (i : Fin r) (a : X ⟶ (A i).X)
    (p : Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) ⟶ (Over.pullback d).obj X) :
    pointsIso q A b d hd
      (Additive.ofMul (p ≫ (Over.pullback d).map a ≫ ProductPoints.CM.factorMap (ProductBaseChange.CM.changedFactors A d) i)) =
        Additive.ofMul (PrimeFieldPoints.CM.pointEquiv b (TransportedGeometricPoints.CM.geometricScalarBase q) d hd X p ≫
          (Over.pullback b).map (a ≫ ProductPoints.CM.factorMap A i)) := by
  have h : (p ≫ (Over.pullback d).map (a ≫ ProductPoints.CM.factorMap A i)) ≫ (ProductBaseChange.CM.productBaseChangeIso A d).hom =
      p ≫ (Over.pullback d).map a ≫ ProductPoints.CM.factorMap (ProductBaseChange.CM.changedFactors A d) i :=
    (Category.assoc _ _ _).trans (congrArg (p ≫ ·)
      (ProductFactorBaseChange.CM.componentMap_baseChange A d i a))
  exact (congrArg (fun z => pointsIso q A b d hd (Additive.ofMul z)) h.symm).trans
    (map_point q A b d hd (a ≫ ProductPoints.CM.factorMap A i) p)

theorem detection_transfer {O J : Type*} (component : O → J)
    (β : O → Additive (Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) ⟶ (GP).X))
    (α : O → Additive (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ (SP).X))
    (hpoints : ∀ x, pointsIso q A b d hd (β x) = α x)
    (hdetect : ∀ f : AbelianScheme.TateComparison.End.IntegralEnd (GP).X,
      (∀ x y : O, component x = component y →
        PointSpecializationFormula.CM.Points.evaluateAt GP (Geometric.PointExt.CM.pointBase (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)) f (β x - β y) = 0) → f = 0)
    (f : AbelianScheme.TateComparison.End.IntegralEnd (SP).X)
    (h : ∀ x y : O, component x = component y →
      PointSpecializationFormula.CM.Points.evaluateAt SP (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q) f (α x - α y) = 0) : f = 0 :=
  @PointTransportDetection.CM.detection_transfer q _ SP GP cmp (cmpG).hom.hom.isMonHom_hom
    O J component β α hpoints hdetect f h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticPointTransport.CM

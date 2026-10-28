import OAI.AlgebraicGeometry.Picard.PoincareBundle.TensorPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Homomorphism
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMaps

/-! # Dual Homomorphism -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.DualHomomorphism

noncomputable section

/-! The actual Poincare products prove that represented dual pullback is a group homomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Homogeneous OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Map OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Homomorphism
open OAI.AlgebraicGeometry.Picard.PoincareBundle.TensorPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.TensorCongruence OAI.AlgebraicGeometry.Picard.PoincareBundle.HorizontalClasses
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters

variable {S : Scheme.{u}} {A B DA DB : Over S} [GrpObj A] [GrpObj B] [GrpObj DA] [GrpObj DB]
  (HA : (Homogeneous.homogeneousSheaf A).obj.RepresentableBy DA)
  (HB : (Homogeneous.homogeneousSheaf B).obj.RepresentableBy DB)
  (P : Line.Bundles.LineBundle (DA ⊗ A).left)
  (Ph : FiberwiseMultiplication.Multiplication (fst DA A) (snd DA A) P)
  (Pv : FiberwiseMultiplication.Multiplication (snd DA A) (fst DA A) P)
  (Q : Line.Bundles.LineBundle (DB ⊗ B).left)
  (Qh : FiberwiseMultiplication.Multiplication (fst DB B) (snd DB B) Q)
  (Qv : FiberwiseMultiplication.Multiplication (snd DB B) (fst DB B) Q)
  (hP : HA.homEquiv (𝟙 DA) = Product.Map.sectionClass P (Vertical.ProductParameters.globalProduct DA A P Pv) (Vertical.ProductParameters.globalProduct_isIso DA A P Pv) (𝟙 DA))
  (hQ : HB.homEquiv (𝟙 DB) = Product.Map.sectionClass Q (Vertical.ProductParameters.globalProduct DB B Q Qv) (Vertical.ProductParameters.globalProduct_isIso DB B Q Qv) (𝟙 DB))
  (f : A ⟶ B) [IsMonHom f]

include hP hQ

omit [GrpObj DA] [GrpObj DB] in
/-- A pulled-back universal class is the universal class of the represented dual image. -/
theorem pulledClass_action {T : Over S} (x : T ⟶ DB) :
    (toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf A)).app (op T)
        ((Homogeneous.pullbackHomogeneousPresheaf f).app (op T)
          (Product.Map.homogeneousClass Q (Vertical.ProductParameters.globalProduct DB B Q Qv) (Vertical.ProductParameters.globalProduct_isIso DB B Q Qv) x)) =
      Product.Map.sectionClass P (Vertical.ProductParameters.globalProduct DA A P Pv) (Vertical.ProductParameters.globalProduct_isIso DA A P Pv)
        (x ≫ DualMaps.representedDualMap HA HB f) := by
  have h := DualMaps.representedDualMap_action HA HB f x
  rw [Product.Homomorphism.universalSection_action P _ _ HA hP, Product.Homomorphism.universalSection_action Q _ _ HB hQ] at h
  exact (TensorPullback.toSheafify_pullback f _).symm.trans h.symm

include Ph Qh

/-- Genuine Poincare tensor products force multiplication preservation on every test scheme. -/
theorem representedDualMap_mul {T : Over S} (x y : T ⟶ DB) :
    (x * y) ≫ DualMaps.representedDualMap HA HB f =
      (x ≫ DualMaps.representedDualMap HA HB f) * (y ≫ DualMaps.representedDualMap HA HB f) := by
  apply HA.homEquiv.injective
  rw [DualMaps.representedDualMap_action, Product.Homomorphism.universalSection_action Q _ _ HB hQ,
    Product.Homomorphism.universalSection_action P _ _ HA hP]
  change (Homogeneous.pullbackHomogeneousSheaf f).hom.app (op T)
      ((toSheafify (Scheme.fppfTopology.over S) (Homogeneous.homogeneousPresheaf B)).app (op T)
        (Product.Map.homogeneousClass Q (Vertical.ProductParameters.globalProduct DB B Q Qv) (Vertical.ProductParameters.globalProduct_isIso DB B Q Qv) (x * y))) = _
  rw [TensorPullback.toSheafify_pullback, HorizontalClasses.homogeneousClass_mul Q (Product.ParameterSchemes.globalProduct DB B Q Qh)
    (Product.ParameterSchemes.globalProduct_isIso DB B Q Qh), TensorPullback.tensorHomogeneous_pullback]
  dsimp only [Product.Map.sectionClass]
  rw [HorizontalClasses.homogeneousClass_mul P (Product.ParameterSchemes.globalProduct DA A P Ph)
    (Product.ParameterSchemes.globalProduct_isIso DA A P Ph)]
  exact TensorCongruence.tensorHomogeneous_congr A (pulledClass_action HA HB P Pv Q Qv hP hQ f x)
    (pulledClass_action HA HB P Pv Q Qv hP hQ f y)

/-- The actual represented dual morphism respects both the product and the unit. -/
theorem representedDualMap_isMonHom : IsMonHom (DualMaps.representedDualMap HA HB f) :=
  MapFromPointProducts.Group.isMonHom _
    (fun _ x y => representedDualMap_mul HA HB P Ph Pv Q Qh Qv hP hQ f x y)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.DualHomomorphism

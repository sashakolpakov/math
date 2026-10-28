import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalTransportAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctor

/-! # Total Level Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap

noncomputable section

/-! An augmented map between coefficient-transported diagrams induces
the corresponding augmented map of original Cech total complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z w' z'
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] {ι : Type} [Finite ι] (U : ι → C)
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (Q : Cᵒᵖ ⥤ CochainComplex B ℕ)
  (α : TotalCoefficient.CechConeTotalCoefficient.mapped F P ⟶ Q)

def map : (F.mapHomologicalComplex (.up ℕ)).obj (Total.CechConeTotal.total U P) ⟶ Total.CechConeTotal.total U Q :=
  (TotalCoefficient.CechConeTotalCoefficient.totalIso F U P).hom ≫ (TotalFunctor.CechConeTotalFunctor.functor U).map α

variable {Z : A} {Z' : B} (e : F.obj Z ≅ Z')
  (η : (Functor.const Cᵒᵖ).obj ((CochainComplex.single₀ A).obj Z) ⟶ P)
  (θ : (Functor.const Cᵒᵖ).obj ((CochainComplex.single₀ B).obj Z') ⟶ Q)
  (h : ∀ V, IntegralComparison.Single.ComplexTransport.map F e (η.app V) ≫ α.app V = θ.app V)

include h in
omit [HasBinaryProducts C] [HasProducts.{0} A] [HasCoproducts.{0} A]
  [HasProducts.{0} B] [HasCoproducts.{0} B] in
theorem cone : TotalTransportAugmentation.CechConeTotalTransportAugmentation.cone F P e η ≫ α = θ := by
  apply NatTrans.ext
  funext V
  exact (congrArg (fun a => a ≫ α.app V)
    (TotalTransportAugmentation.CechConeTotalTransportAugmentation.cone_app F P e η V)).trans (h V)

include h in
theorem augmentation : IntegralComparison.Single.ComplexTransport.map F e
    (Total.CechConeTotal.augmentation U P ((CochainComplex.single₀ A).obj Z) η) ≫ CechConeTotalLevelMap.map F U P Q α =
      Total.CechConeTotal.augmentation U Q ((CochainComplex.single₀ B).obj Z') θ := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (TotalFunctor.CechConeTotalFunctor.functor U).map α)
      (TotalTransportAugmentation.CechConeTotalTransportAugmentation.augmentation F U P e η)).trans
        ((TotalFunctor.CechConeTotalFunctor.augmentation U _ _ α).trans
          (congrArg (fun η' => Total.CechConeTotal.augmentation U Q ((CochainComplex.single₀ B).obj Z') η')
            (cone F P Q α e η θ h))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap

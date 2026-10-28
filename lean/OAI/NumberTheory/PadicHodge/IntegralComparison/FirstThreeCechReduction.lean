import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.MappedTotalNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.QuotientProjection

/-! # First Three Cech Reduction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FirstThreeCechReduction

noncomputable section

/-! Truncation to the first three form degrees commutes with the
literal coefficient reduction of the original Čech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v
variable (R : Type) [CommRing R] (I : Ideal R)
  {C : Type u} [Category.{v} C]
  (E : SimplicialObject (FormalCoproduct.{0} C))

local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient.functor R I
local notation "G" => FormalCoproduct.cochainComplexFunctor E
local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.presheaves (C := C) Q ⋙ G

def presheafProjection : 𝟭 (Cᵒᵖ ⥤ ModuleCat.{0} R) ⟶
    GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.presheaves (C := C) Q where
  app P := Functor.whiskerLeft P (Module.IdealQuotient.projection R I)
  naturality _ _ f := by
    apply NatTrans.ext
    funext V
    exact (Module.IdealQuotient.projection R I).naturality (f.app V)

def rows : G ⟶ H := Functor.whiskerRight (presheafProjection R I) G

variable (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0} R) ℕ)

theorem map_eq : GeometricComparison.FirstThree.MappedTotalNaturality.FirstThreeMappedTotalNaturality.map R G H (rows R I E) K =
    GeometricComparison.CechPresheaf.QuotientProjection.CechPresheafQuotientProjection.map R I E K := by
  apply congrArg (fun f => HomologicalComplex₂.total.map f (.up ℕ))
  apply HomologicalComplex.Hom.ext
  funext q
  rfl

theorem natural :
    GeometricComparison.FirstThree.MappedTotalOne.FirstThreeMappedTotalHOne.map R G K ≫
      GeometricComparison.CechPresheaf.QuotientProjection.CechPresheafQuotientProjection.map R I E (GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex K) =
    GeometricComparison.CechPresheaf.QuotientProjection.CechPresheafQuotientProjection.map R I E K ≫
      GeometricComparison.FirstThree.MappedTotalOne.FirstThreeMappedTotalHOne.map R H K := by
  rw [← map_eq, ← map_eq]
  exact GeometricComparison.FirstThree.MappedTotalNaturality.FirstThreeMappedTotalNaturality.natural R G H (rows R I E) K

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FirstThreeCechReduction

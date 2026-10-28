import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ProjectionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CechIntersections

/-! # Pushforward Factors -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.PushforwardFactors

noncomputable section

/- Adapted for HilbertConstruction with explicit coefficient rings and the existing coefficient section comparison. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

theorem preimageCechIntersection {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type u} (U : ι → Y.Opens) (n : ℕ) (i : Fin (n + 1) → ι) :
    f ⁻¹ᵁ (∏ᶜ fun k : Fin (n + 1) => U (i k)) =
      ∏ᶜ fun k : Fin (n + 1) => f ⁻¹ᵁ U (i k) := by
  rw [Affine.CechIntersections.opensProduct_eq_iInf, Affine.CechIntersections.opensProduct_eq_iInf]
  ext x
  rw [TopologicalSpace.Opens.coe_iInf]
  change f x ∈ (((⨅ k, U (i k)) : Y.Opens) : Set Y) ↔ _
  rw [TopologicalSpace.Opens.coe_iInf]
  simp

def coefficientModulePresheafPushforwardAppIso
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Y)
    (coefficientMap : R →+* Γ(Y, ⊤)) (M : X.Modules) (V : Y.Opens) :
    (Coefficient.ModulePresheaf.coefficientModulePresheaf (f.appTop.hom.comp coefficientMap) M).obj (op (f ⁻¹ᵁ V)) ≅
      (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap ((Scheme.Modules.pushforward f).obj M)).obj (op V) :=
  (Coefficient.PushforwardSections.coefficientPushforwardSectionEquiv f coefficientMap M V).symm.toModuleIso

/-- Each Cech factor on the inverse-image cover agrees with the corresponding factor of the
pushforward. -/
noncomputable def coefficientCechFactorPushforwardIso
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Y) (coefficientMap : R →+* Γ(Y, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → Y.Opens) (n : ℕ) (i : Fin (n + 1) → ι) :
    Ordered.CoefficientCechTerms.coefficientCechFactor (f.appTop.hom.comp coefficientMap) M (fun j ↦ f ⁻¹ᵁ U j) n i ≅
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap ((Scheme.Modules.pushforward f).obj M) U n i :=
  (Coefficient.ModulePresheaf.coefficientModulePresheaf (f.appTop.hom.comp coefficientMap) M).mapIso
      (eqToIso (preimageCechIntersection f U n i)).op ≪≫
    coefficientModulePresheafPushforwardAppIso f coefficientMap M
      (∏ᶜ fun k : Fin (n + 1) => U (i k))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.PushforwardFactors

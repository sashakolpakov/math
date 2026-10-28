import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.TopCone
import OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechGlobal

/-! # Cech Top Cone Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechTopConeCoordinates.FlasqueCechTopConeCoordinates

noncomputable section

/-! The canonical presheaf-complex cone edge is exactly the original
global-to-Cech map for the underlying flasque complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u v w
variable (R : Type u) [CommRing R] (X : TopCat.{v})
  {ι : Type} (U : ι → Opens X)
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v w} R)) ℕ)

local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechGlobal.FlasqueCechGlobalComparison.presheafComplex R X K

theorem map_eq : CechPresheaf.ConeTotal.CechPresheafConeTotal.map U P ((CechPresheaf.TopCone.CechPresheafTopCone.global (Opens X)).obj P)
    (CechPresheaf.TopCone.CechPresheafTopCone.cone (Opens X) P) = FlasqueCechGlobal.FlasqueCechGlobalComparison.map R X U K := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechTopConeCoordinates.FlasqueCechTopConeCoordinates

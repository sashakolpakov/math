import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedHomotopy

/-! # Cohomology Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CohomologyNaturality.CechConeHOneNaturality

noncomputable section

/-! Cone naturality in the same original typed Cech H-one
interface used by the geometric comparison homotopy. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v s t
variable (R : Type u) [CommRing R]
  {C : Type s} [Category.{t} C] [HasBinaryProducts C] {ι : Type} (U : ι → C)
  {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ}
  {M N : CochainComplex (ModuleCat.{max u v} R) ℕ}
  (η : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := C)).obj M ⟶ K)
  (θ : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := C)).obj N ⟶ L)
  (a : K ⟶ L) (b : M ⟶ N)
  (h : η ≫ a = (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := C)).map b ≫ θ)

include h in
theorem homology : HomologicalComplex.homologyMap (CechPresheaf.ConeTotal.CechPresheafConeTotal.map U K M η) 1 ≫
    CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne R U a =
      HomologicalComplex.homologyMap b 1 ≫
        HomologicalComplex.homologyMap (CechPresheaf.ConeTotal.CechPresheafConeTotal.map U L N θ) 1 :=
  (HomologicalComplex.homologyMap_comp _ _ 1).symm.trans
    ((congrArg (fun c => HomologicalComplex.homologyMap c 1)
      (CechPresheaf.ConeNaturality.CechPresheafConeNaturality.naturality U η θ a b h)).trans
        (HomologicalComplex.homologyMap_comp _ _ 1))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CohomologyNaturality.CechConeHOneNaturality

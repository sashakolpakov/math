import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConeTotalMapCoordinates

/-! # Cone Total Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConeTotalNaturality

noncomputable section

/-! Cone naturality for the original Cech total map, before choosing
coefficient complexes or taking their geometric realizations. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v s t
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {ι : Type} (U : ι → C)
  {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ}
  {M N : CochainComplex (ModuleCat.{max u v} R) ℕ}
  (η : (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := C)).obj M ⟶ K)
  (θ : (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := C)).obj N ⟶ L)
  (a : K ⟶ L) (b : M ⟶ N)
  (h : η ≫ a = (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := C)).map b ≫ θ)

include h in
theorem naturality :
    GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map U K M η ≫ AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map R (NonemptyCechNerve.nerve U) a =
      b ≫ GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map U L N θ :=
  GeometricComparison.CechPresheaf.ConeNaturality.CechPresheafConeNaturality.naturality U η θ a b h

include h in
theorem homology (q : ℕ) :
    homologyMap (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map U K M η) q ≫
      homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map R (NonemptyCechNerve.nerve U) a) q =
    homologyMap b q ≫ homologyMap (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map U L N θ) q :=
  (homologyMap_comp _ _ q).symm.trans
    ((congrArg (fun f => homologyMap f q) (naturality R U η θ a b h)).trans
      (homologyMap_comp _ _ q))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConeTotalNaturality

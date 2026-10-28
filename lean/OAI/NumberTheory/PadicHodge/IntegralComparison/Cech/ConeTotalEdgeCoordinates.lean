import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConeTotalNaturality

/-! # Cone Total Edge Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConeTotalEdgeCoordinates

noncomputable section

/-! Cone naturality retains specified original edge maps before
passing to homology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
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
  (sourceEdge : M ⟶ (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U K).total (.up ℕ))
  (targetEdge : N ⟶ (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U L).total (.up ℕ))
  (hs : sourceEdge = GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map U K M η)
  (ht : targetEdge = GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map U L N θ)

include h hs ht in
theorem homology (q : ℕ) :
    homologyMap sourceEdge q ≫ homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map R (NonemptyCechNerve.nerve U) a) q =
      homologyMap b q ≫ homologyMap targetEdge q := by
  subst sourceEdge
  subst targetEdge
  exact ConeTotalNaturality.homology R U η θ a b h q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConeTotalEdgeCoordinates

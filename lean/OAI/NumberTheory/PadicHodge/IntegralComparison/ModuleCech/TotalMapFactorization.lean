import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.TotalMapCoordinates

/-! # Total Map Factorization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.TotalMapFactorization

noncomputable section

/-! Substitute the raw Čech total map inside a homology factorization
before specializing the coefficient complexes and output group. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v s t
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {ι : Type} (U : ι → C)
  {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ} (a : K ⟶ L) (q : ℕ)

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

theorem homology
    {f : (TotalMapCoordinates.total R U K).homology q ⟶
      (TotalMapCoordinates.total R U L).homology q}
    (h : f = homologyMap (TotalMapCoordinates.map R U a) q) :
    f = homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map R (NonemptyCechNerve.nerve U) a) q :=
  h.trans (TotalMapCoordinates.homology_map R U a q)

theorem comparison {T : ModuleCat.{max u v} R}
    (b : (TotalMapCoordinates.total R U L).homology q ⟶ T)
    {f : (TotalMapCoordinates.total R U K).homology q ⟶ T}
    (h : f = homologyMap (TotalMapCoordinates.map R U a) q ≫ b) :
    f = homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map R (NonemptyCechNerve.nerve U) a) q ≫ b :=
  h.trans (TotalMapCoordinates.composition R U a q b)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.TotalMapFactorization

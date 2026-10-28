import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.TotalMapFactorization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers

/-! # Cech Total Map Factorization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CechTotalMapFactorization

noncomputable section

/-! Čech-total factorization with the native Witt coefficient category
fixed before choosing the coefficient complexes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

universe s t
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {ι : Type} (U : ι → C)

def total (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ) :
    CochainComplex (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ :=
  (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U K).total (.up ℕ)

def map {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ} (a : K ⟶ L) :
    CechTotalMapFactorization.total p k U K ⟶ CechTotalMapFactorization.total p k U L :=
  ModuleCech.TotalMapCoordinates.map.{1,2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) U a

variable {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ}
  (a : K ⟶ L) (q : ℕ)

omit [Fintype k] [CharP k p] in
theorem comparison {T : ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))}
    (b : (CechTotalMapFactorization.total p k U L).homology q ⟶ T)
    {f : (CechTotalMapFactorization.total p k U K).homology q ⟶ T}
    (h : f = homologyMap (map p k U a) q ≫ b) :
    f = homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1,2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (NonemptyCechNerve.nerve U) a) q ≫ b :=
  ModuleCech.TotalMapFactorization.comparison.{1,2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) U a q b h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CechTotalMapFactorization

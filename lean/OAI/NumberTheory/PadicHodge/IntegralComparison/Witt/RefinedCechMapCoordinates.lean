import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CechTotalMapFactorization
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined

/-! # Refined Cech Map Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.RefinedCechMapCoordinates

noncomputable section

/-! The original refined Čech total with its native Witt coefficient category
fixed before the coefficient complexes are chosen. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

universe s t
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {ι : Type} (U : ι → C)

def bicomplexFunctor : CochainComplex (Cᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ ⥤
    HomologicalComplex₂ (ModuleCat.{2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) (.up ℕ) (.up ℕ) :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.bicomplex.{1,2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (NonemptyCechNerve.nerve U)

def total (K : CochainComplex (Cᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ) :
    CochainComplex (ModuleCat.{2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ :=
  ((bicomplexFunctor p k U).obj K).total (.up ℕ)

def map {K L : CochainComplex (Cᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ}
    (a : K ⟶ L) : RefinedCechMapCoordinates.total p k U K ⟶ RefinedCechMapCoordinates.total p k U L :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.map.{1,2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) U a

variable {K L : CochainComplex (Cᵒᵖ ⥤
  ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ}
  (a : K ⟶ L) (q : ℕ)

omit [Fintype k] [CharP k p] in
theorem comparison
    {T : ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))}
    (b : (RefinedCechMapCoordinates.total p k U L).homology q ⟶ T)
    {f : (RefinedCechMapCoordinates.total p k U K).homology q ⟶ T}
    (h : f = homologyMap (map p k U a) q ≫ b) :
    f = homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.map.{1,2}
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) U a) q ≫ b := h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.RefinedCechMapCoordinates

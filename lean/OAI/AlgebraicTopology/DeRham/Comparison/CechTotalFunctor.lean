import OAI.AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexSigns

/-! # Cech Total Functor -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CechTotalFunctor

noncomputable section

/-!
# The total Čech functor on actual presheaf complexes

This uses the existing Čech bicomplex and mathlib totalization. Its maps
apply the given coefficient map on each actual section summand.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X ι : Type u} [TopologicalSpace X] (U : ι → Opens X)

/-- Actual presheaf complexes map functorially to their signed Čech total complexes. -/
def cechTotalFunctor :
    CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ) ℕ ⥤
      CochainComplex (ModuleCat.{u} ℂ) ℕ :=
  CechDoubleComplexFunctor.cechDoubleComplexFunctor U ⋙ HomologicalComplex₂.totalFunctor
    (ModuleCat.{u} ℂ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)

/-- The signed total complex of actual Čech sections of a presheaf complex. -/
abbrev cechTotalComplex (K : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ) ℕ) :=
  (cechTotalFunctor U).obj K

variable (K : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ) ℕ)

/-- Inclusion of an actual section-family summand in the total complex. -/
def cechTotalInclusion (p q n : ℕ) (h : p + q = n) :
    ModuleCat.of ℂ (SmoothCech.CechCochain (K.X q) U p) ⟶ (cechTotalComplex U K).X n :=
  (CechDoubleComplexFunctor.cechDoubleComplex U K).ιTotal (ComplexShape.up ℕ) p q n h

/-- The total differential is the signed sum of the two actual differentials. -/
theorem cechTotalInclusion_d (p q n : ℕ) (h : p + q = n) :
    cechTotalInclusion U K p q n h ≫ (cechTotalComplex U K).d n (n + 1) =
      ModuleCat.ofHom (SmoothCech.cechDelta (K.X q) U p) ≫
          cechTotalInclusion U K (p + 1) q (n + 1) (by omega) +
        ((-1 : ℤ) ^ p) • (ModuleCat.ofHom (SmoothCechDoubleComplex.cechCoefficientMap U (K.d q (q + 1)) p) ≫
          cechTotalInclusion U K p (q + 1) (n + 1) (by omega)) := by
  have hd := DoubleComplexSigns.DoubleComplex.iota_d_of_eq (CechDoubleComplexFunctor.cechDoubleComplex U K) p q n h
  rw [CechDoubleComplexFunctor.cechDoubleComplex_d_f, CechDoubleComplexFunctor.cechDoubleComplex_X_d] at hd
  exact hd

variable {K}
variable {L N : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ) ℕ}

/-- A genuine coefficient cochain map induces the actual map on Čech total complexes. -/
abbrev cechTotalMap (φ : K ⟶ L) : cechTotalComplex U K ⟶ cechTotalComplex U L :=
  (cechTotalFunctor U).map φ

/-- The total map is the supplied coefficient map on every actual section summand. -/
theorem cechTotalInclusion_map (φ : K ⟶ L) (p q n : ℕ) (h : p + q = n) :
    cechTotalInclusion U K p q n h ≫ (cechTotalMap U φ).f n =
      ModuleCat.ofHom (SmoothCechDoubleComplex.cechCoefficientMap U (φ.f q) p) ≫ cechTotalInclusion U L p q n h :=
  HomologicalComplex₂.ιTotal_map (K := CechDoubleComplexFunctor.cechDoubleComplex U K)
    (L := CechDoubleComplexFunctor.cechDoubleComplex U L) (φ := CechDoubleComplexFunctor.cechDoubleComplexMap U φ)
    (c₁₂ := ComplexShape.up ℕ) p q n h

@[simp]
theorem cechTotalMap_id : cechTotalMap U (𝟙 K) = 𝟙 (cechTotalComplex U K) :=
  (cechTotalFunctor U).map_id K

@[simp]
theorem cechTotalMap_comp (φ : K ⟶ L) (ψ : L ⟶ N) :
    cechTotalMap U (φ ≫ ψ) = cechTotalMap U φ ≫ cechTotalMap U ψ :=
  (cechTotalFunctor U).map_comp φ ψ

end

end OAI.AlgebraicTopology.DeRham.Comparison.CechTotalFunctor

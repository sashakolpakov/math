import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ComponentHomology

/-! # Cochain Component -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CochainComponent.CochainComponentHomologySquare

noncomputable section

/-! A square at the relevant cochain degree induces the original
homology square, including a side with three successive maps. -/

open _root_.CategoryTheory

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]
  {K L M N P : CochainComplex A ℕ}

theorem pair (a : K ⟶ L) (b : L ⟶ M) (c : K ⟶ N) (d : N ⟶ M)
    (i : ℕ) (h : a.f i ≫ b.f i = c.f i ≫ d.f i) :
    HomologicalComplex.homologyMap a i ≫ HomologicalComplex.homologyMap b i =
      HomologicalComplex.homologyMap c i ≫ HomologicalComplex.homologyMap d i := by
  have hh := CechPresheaf.ComponentHomology.CechPresheafComponentHomology.homology_of_component (a ≫ b) (c ≫ d) i h
  simpa only [HomologicalComplex.homologyMap_comp] using hh

theorem triple (a : K ⟶ L) (b : L ⟶ M) (c : M ⟶ N) (d : K ⟶ P) (e : P ⟶ N)
    (i : ℕ) (h : a.f i ≫ b.f i ≫ c.f i = d.f i ≫ e.f i) :
    HomologicalComplex.homologyMap a i ≫ HomologicalComplex.homologyMap b i ≫
      HomologicalComplex.homologyMap c i =
        HomologicalComplex.homologyMap d i ≫ HomologicalComplex.homologyMap e i := by
  have hh := CechPresheaf.ComponentHomology.CechPresheafComponentHomology.homology_of_component (a ≫ b ≫ c) (d ≫ e) i h
  simpa only [HomologicalComplex.homologyMap_comp] using hh

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CochainComponent.CochainComponentHomologySquare

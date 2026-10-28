import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections

/-! # Double Complex Map Components -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMapComponents.DoubleComplex

noncomputable section

/-!
# Component formulas for maps of actual total complexes

These identities concern mathlib's native bicomplex morphisms and total-map
construction, together with the established coproduct projections. They
express that totalization acts on each bidegree by the given component map.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u v

variable {R : Type u} [Ring R]
variable {K L : HomologicalComplex₂ (ModuleCat.{v} R)
  (ComplexShape.up ℕ) (ComplexShape.up ℕ)}

/-- Naturality of an actual coproduct inclusion under the totalized map. -/
@[reassoc]
theorem iota_total_map (φ : K ⟶ L) (p q n : ℕ) (h : p + q = n) :
    K.ιTotal (ComplexShape.up ℕ) p q n h ≫
        (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n =
      (φ.f p).f q ≫ L.ιTotal (ComplexShape.up ℕ) p q n h :=
  HomologicalComplex₂.ιTotal_map (K := K) (L := L) (φ := φ)
    (c₁₂ := ComplexShape.up ℕ) p q n h

/-- On an element of a summand, the total map applies its bidegree component. -/
theorem total_map_iota (φ : K ⟶ L) (p q n : ℕ) (h : p + q = n)
    (x : (K.X p).X q) :
    (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n
        (K.ιTotal (ComplexShape.up ℕ) p q n h x) =
      L.ιTotal (ComplexShape.up ℕ) p q n h ((φ.f p).f q x) :=
  ConcreteCategory.congr_hom (iota_total_map φ p q n h) x

/-- The same inclusion naturality includes mismatched total degrees, where
both inclusion maps are the actual zero morphisms. -/
@[reassoc]
theorem iotaOrZero_total_map (φ : K ⟶ L) (p q n : ℕ) :
    K.ιTotalOrZero (ComplexShape.up ℕ) p q n ≫
        (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n =
      (φ.f p).f q ≫ L.ιTotalOrZero (ComplexShape.up ℕ) p q n :=
  HomologicalComplex₂.ιTotalOrZero_map (K := K) (L := L) (φ := φ)
    (c₁₂ := ComplexShape.up ℕ) p q n

theorem total_map_iotaOrZero (φ : K ⟶ L) (p q n : ℕ) (x : (K.X p).X q) :
    (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n
        (K.ιTotalOrZero (ComplexShape.up ℕ) p q n x) =
      L.ιTotalOrZero (ComplexShape.up ℕ) p q n ((φ.f p).f q x) :=
  ConcreteCategory.congr_hom (iotaOrZero_total_map φ p q n) x

/-- Projection onto a bidegree commutes with the native totalized map. -/
@[reassoc]
theorem total_map_πTotal (φ : K ⟶ L) (p q n : ℕ) (h : p + q = n) :
    (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n ≫ DoubleComplexProjections.DoubleComplex.πTotal L p q n h =
      DoubleComplexProjections.DoubleComplex.πTotal K p q n h ≫ (φ.f p).f q := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  rw [iota_total_map_assoc]
  by_cases hpair : (a, b) = (p, q)
  · have ha : a = p := congrArg Prod.fst hpair
    have hb : b = q := congrArg Prod.snd hpair
    subst a
    subst b
    simp only [DoubleComplexProjections.DoubleComplex.iota_πTotal_self, DoubleComplexProjections.DoubleComplex.iota_πTotal_self_assoc, Category.comp_id]
  · rw [DoubleComplexProjections.DoubleComplex.iota_πTotal_ne L a b p q n hab h hpair,
      DoubleComplexProjections.DoubleComplex.iota_πTotal_ne_assoc K a b p q n hab h hpair, comp_zero, zero_comp]

/-- The element-level projection formula for the actual totalized map. -/
theorem project_total_map (φ : K ⟶ L) (p q n : ℕ) (h : p + q = n)
    (x : (K.total (ComplexShape.up ℕ)).X n) :
    DoubleComplexProjections.DoubleComplex.πTotal L p q n h ((HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n x) =
      (φ.f p).f q (DoubleComplexProjections.DoubleComplex.πTotal K p q n h x) :=
  ConcreteCategory.congr_hom (total_map_πTotal φ p q n h) x

/-- Naturality of the projection extended by zero to every total degree. -/
@[reassoc]
theorem total_map_πTotalOrZero (φ : K ⟶ L) (p q n : ℕ) :
    (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n ≫ DoubleComplexProjections.DoubleComplex.πTotalOrZero L p q n =
      DoubleComplexProjections.DoubleComplex.πTotalOrZero K p q n ≫ (φ.f p).f q := by
  by_cases h : p + q = n
  · rw [DoubleComplexProjections.DoubleComplex.πTotalOrZero_eq L p q n h, DoubleComplexProjections.DoubleComplex.πTotalOrZero_eq K p q n h]
    exact total_map_πTotal φ p q n h
  · rw [DoubleComplexProjections.DoubleComplex.πTotalOrZero_eq_zero L p q n h, DoubleComplexProjections.DoubleComplex.πTotalOrZero_eq_zero K p q n h,
      comp_zero, zero_comp]

theorem projectOrZero_total_map (φ : K ⟶ L) (p q n : ℕ)
    (x : (K.total (ComplexShape.up ℕ)).X n) :
    DoubleComplexProjections.DoubleComplex.πTotalOrZero L p q n ((HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n x) =
      (φ.f p).f q (DoubleComplexProjections.DoubleComplex.πTotalOrZero K p q n x) :=
  ConcreteCategory.congr_hom (total_map_πTotalOrZero φ p q n) x

end

end OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMapComponents.DoubleComplex

import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections

/-! # Double Complex Differential -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexDifferential.DoubleComplex

noncomputable section

/-!
# Components of the differential of a first-quadrant total complex

These formulas use the inclusions and projections of mathlib's actual total
complex. A summand contributes only to its horizontal and vertical successors.
An arbitrary differential component is the sum of the incoming horizontal
component and the signed incoming vertical component. At the two boundary
axes only the existing incoming component remains.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u v

variable {R : Type u} [Ring R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

/-- The horizontal matrix entry of the total differential. -/
@[reassoc]
theorem iota_d_πTotal_horizontal (p q n : ℕ) (h : p + q = n) :
    K.ιTotal (ComplexShape.up ℕ) p q n h ≫
        (K.total (ComplexShape.up ℕ)).d n (n + 1) ≫
        DoubleComplexProjections.DoubleComplex.πTotal K (p + 1) q (n + 1) (by omega) =
      (K.d p (p + 1)).f q := by
  rw [← Category.assoc, DoubleComplexSigns.DoubleComplex.iota_d_of_eq]
  simp only [add_comp, zsmul_comp, Category.assoc]
  rw [DoubleComplexProjections.DoubleComplex.iota_πTotal_self,
    DoubleComplexProjections.DoubleComplex.iota_πTotal_ne K p (q + 1) (p + 1) q (n + 1) _ _ (by
      intro he
      have := (Prod.mk.inj he).1
      omega)]
  simp only [Category.comp_id, comp_zero, smul_zero, add_zero]

/-- The vertical matrix entry carries the sign of the source horizontal degree. -/
@[reassoc]
theorem iota_d_πTotal_vertical (p q n : ℕ) (h : p + q = n) :
    K.ιTotal (ComplexShape.up ℕ) p q n h ≫
        (K.total (ComplexShape.up ℕ)).d n (n + 1) ≫
        DoubleComplexProjections.DoubleComplex.πTotal K p (q + 1) (n + 1) (by omega) =
      ((-1 : ℤ) ^ p) • (K.X p).d q (q + 1) := by
  rw [← Category.assoc, DoubleComplexSigns.DoubleComplex.iota_d_of_eq]
  simp only [add_comp, zsmul_comp, Category.assoc]
  rw [DoubleComplexProjections.DoubleComplex.iota_πTotal_ne K (p + 1) q p (q + 1) (n + 1) _ _ (by
      intro he
      have := (Prod.mk.inj he).1
      omega), DoubleComplexProjections.DoubleComplex.iota_πTotal_self]
  simp only [Category.comp_id, comp_zero, zero_add]

/-- Every other matrix entry of the total differential is zero. -/
@[reassoc]
theorem iota_d_πTotal_ne (p q a b n : ℕ) (h : p + q = n)
    (hab : a + b = n + 1)
    (hh : (p + 1, q) ≠ (a, b)) (hv : (p, q + 1) ≠ (a, b)) :
    K.ιTotal (ComplexShape.up ℕ) p q n h ≫
        (K.total (ComplexShape.up ℕ)).d n (n + 1) ≫
        DoubleComplexProjections.DoubleComplex.πTotal K a b (n + 1) hab = 0 := by
  rw [← Category.assoc, DoubleComplexSigns.DoubleComplex.iota_d_of_eq]
  simp only [add_comp, zsmul_comp, Category.assoc]
  rw [DoubleComplexProjections.DoubleComplex.iota_πTotal_ne K (p + 1) q a b (n + 1) _ hab hh,
    DoubleComplexProjections.DoubleComplex.iota_πTotal_ne K p (q + 1) a b (n + 1) _ hab hv]
  simp only [comp_zero, smul_zero, add_zero]

/-- An interior component is the sum of the two incoming differential components. -/
@[reassoc]
theorem d_πTotal_succ_succ (p q n : ℕ) (h : (p + 1) + (q + 1) = n + 1) :
    (K.total (ComplexShape.up ℕ)).d n (n + 1) ≫
        DoubleComplexProjections.DoubleComplex.πTotal K (p + 1) (q + 1) (n + 1) h =
      DoubleComplexProjections.DoubleComplex.πTotal K p (q + 1) n (by omega) ≫ (K.d p (p + 1)).f (q + 1) +
        ((-1 : ℤ) ^ (p + 1)) •
          (DoubleComplexProjections.DoubleComplex.πTotal K (p + 1) q n (by omega) ≫ (K.X (p + 1)).d q (q + 1)) := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  change a + b = n at hab
  by_cases ha : a = p
  · subst a
    have hb : b = q + 1 := by omega
    subst b
    rw [iota_d_πTotal_horizontal]
    simp only [comp_add, comp_zsmul, ← Category.assoc, DoubleComplexProjections.DoubleComplex.iota_πTotal_self,
      DoubleComplexProjections.DoubleComplex.iota_πTotal_ne K p (q + 1) (p + 1) q n hab _ (by
        intro he
        have := (Prod.mk.inj he).1
        omega), Category.id_comp, zero_comp, smul_zero, add_zero]
  · by_cases ha' : a = p + 1
    · subst a
      have hb : b = q := by omega
      subst b
      rw [iota_d_πTotal_vertical]
      simp only [comp_add, comp_zsmul, ← Category.assoc, DoubleComplexProjections.DoubleComplex.iota_πTotal_self,
        DoubleComplexProjections.DoubleComplex.iota_πTotal_ne K (p + 1) q p (q + 1) n hab _ (by
          intro he
          have := (Prod.mk.inj he).1
          omega), Category.id_comp, zero_comp, zero_add]
    · rw [iota_d_πTotal_ne K a b (p + 1) (q + 1) n hab h (by
          intro he
          exact ha (by have := (Prod.mk.inj he).1; omega)) (by
          intro he
          exact ha' (Prod.mk.inj he).1)]
      simp only [comp_add, comp_zsmul, ← Category.assoc,
        DoubleComplexProjections.DoubleComplex.iota_πTotal_ne K a b p (q + 1) n hab _ (by
          intro he
          exact ha (Prod.mk.inj he).1),
        DoubleComplexProjections.DoubleComplex.iota_πTotal_ne K a b (p + 1) q n hab _ (by
          intro he
          exact ha' (Prod.mk.inj he).1), zero_comp, smul_zero, add_zero]

/-- Along the zero vertical degree, only the horizontal incoming component exists. -/
@[reassoc]
theorem d_πTotal_succ_zero (p n : ℕ) (h : (p + 1) + 0 = n + 1) :
    (K.total (ComplexShape.up ℕ)).d n (n + 1) ≫
        DoubleComplexProjections.DoubleComplex.πTotal K (p + 1) 0 (n + 1) h =
      DoubleComplexProjections.DoubleComplex.πTotal K p 0 n (by omega) ≫ (K.d p (p + 1)).f 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  change a + b = n at hab
  by_cases ha : a = p
  · subst a
    have hb : b = 0 := by omega
    subst b
    rw [iota_d_πTotal_horizontal]
    simp only [← Category.assoc, DoubleComplexProjections.DoubleComplex.iota_πTotal_self, Category.id_comp]
  · rw [iota_d_πTotal_ne K a b (p + 1) 0 n hab h (by
        intro he
        exact ha (by have := (Prod.mk.inj he).1; omega)) (by
        intro he
        have := (Prod.mk.inj he).2
        omega)]
    rw [← Category.assoc, DoubleComplexProjections.DoubleComplex.iota_πTotal_ne K a b p 0 n hab _ (by
      intro he
      exact ha (Prod.mk.inj he).1), zero_comp]

/-- Along the zero horizontal degree, only the unsigned vertical component exists. -/
@[reassoc]
theorem d_πTotal_zero_succ (q n : ℕ) (h : 0 + (q + 1) = n + 1) :
    (K.total (ComplexShape.up ℕ)).d n (n + 1) ≫
        DoubleComplexProjections.DoubleComplex.πTotal K 0 (q + 1) (n + 1) h =
      DoubleComplexProjections.DoubleComplex.πTotal K 0 q n (by omega) ≫ (K.X 0).d q (q + 1) := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  change a + b = n at hab
  by_cases ha : a = 0
  · subst a
    have hb : b = q := by omega
    subst b
    rw [iota_d_πTotal_vertical]
    simp only [← Category.assoc, DoubleComplexProjections.DoubleComplex.iota_πTotal_self, Category.id_comp, pow_zero, one_smul]
  · rw [iota_d_πTotal_ne K a b 0 (q + 1) n hab h (by
        intro he
        have := (Prod.mk.inj he).1
        omega) (by
        intro he
        exact ha (Prod.mk.inj he).1)]
    rw [← Category.assoc, DoubleComplexProjections.DoubleComplex.iota_πTotal_ne K a b 0 q n hab _ (by
      intro he
      exact ha (Prod.mk.inj he).1), zero_comp]

/-- Element form of the horizontal matrix entry. -/
theorem project_d_iota_horizontal (p q n : ℕ) (h : p + q = n)
    (x : (K.X p).X q) :
    DoubleComplexProjections.DoubleComplex.πTotal K (p + 1) q (n + 1) (by omega)
        ((K.total (ComplexShape.up ℕ)).d n (n + 1)
          (K.ιTotal (ComplexShape.up ℕ) p q n h x)) =
      (K.d p (p + 1)).f q x :=
  ConcreteCategory.congr_hom (iota_d_πTotal_horizontal K p q n h) x

/-- Element form of the signed vertical matrix entry. -/
theorem project_d_iota_vertical (p q n : ℕ) (h : p + q = n)
    (x : (K.X p).X q) :
    DoubleComplexProjections.DoubleComplex.πTotal K p (q + 1) (n + 1) (by omega)
        ((K.total (ComplexShape.up ℕ)).d n (n + 1)
          (K.ιTotal (ComplexShape.up ℕ) p q n h x)) =
      ((-1 : ℤ) ^ p) • (K.X p).d q (q + 1) x :=
  ConcreteCategory.congr_hom (iota_d_πTotal_vertical K p q n h) x

/-- A differential of an included element has no other components. -/
theorem project_d_iota_ne (p q a b n : ℕ) (h : p + q = n)
    (hab : a + b = n + 1)
    (hh : (p + 1, q) ≠ (a, b)) (hv : (p, q + 1) ≠ (a, b))
    (x : (K.X p).X q) :
    DoubleComplexProjections.DoubleComplex.πTotal K a b (n + 1) hab
        ((K.total (ComplexShape.up ℕ)).d n (n + 1)
          (K.ιTotal (ComplexShape.up ℕ) p q n h x)) = 0 :=
  ConcreteCategory.congr_hom (iota_d_πTotal_ne K p q a b n h hab hh hv) x

/-- The interior component formula for any element of the actual total complex. -/
theorem project_d_succ_succ (p q n : ℕ) (h : (p + 1) + (q + 1) = n + 1)
    (x : (K.total (ComplexShape.up ℕ)).X n) :
    DoubleComplexProjections.DoubleComplex.πTotal K (p + 1) (q + 1) (n + 1) h
        ((K.total (ComplexShape.up ℕ)).d n (n + 1) x) =
      (K.d p (p + 1)).f (q + 1) (DoubleComplexProjections.DoubleComplex.πTotal K p (q + 1) n (by omega) x) +
        ((-1 : ℤ) ^ (p + 1)) •
          (K.X (p + 1)).d q (q + 1) (DoubleComplexProjections.DoubleComplex.πTotal K (p + 1) q n (by omega) x) :=
  ConcreteCategory.congr_hom (d_πTotal_succ_succ K p q n h) x

/-- The component formula on the zero vertical boundary. -/
theorem project_d_succ_zero (p n : ℕ) (h : (p + 1) + 0 = n + 1)
    (x : (K.total (ComplexShape.up ℕ)).X n) :
    DoubleComplexProjections.DoubleComplex.πTotal K (p + 1) 0 (n + 1) h ((K.total (ComplexShape.up ℕ)).d n (n + 1) x) =
      (K.d p (p + 1)).f 0 (DoubleComplexProjections.DoubleComplex.πTotal K p 0 n (by omega) x) :=
  ConcreteCategory.congr_hom (d_πTotal_succ_zero K p n h) x

/-- The component formula on the zero horizontal boundary. -/
theorem project_d_zero_succ (q n : ℕ) (h : 0 + (q + 1) = n + 1)
    (x : (K.total (ComplexShape.up ℕ)).X n) :
    DoubleComplexProjections.DoubleComplex.πTotal K 0 (q + 1) (n + 1) h ((K.total (ComplexShape.up ℕ)).d n (n + 1) x) =
      (K.X 0).d q (q + 1) (DoubleComplexProjections.DoubleComplex.πTotal K 0 q n (by omega) x) :=
  ConcreteCategory.congr_hom (d_πTotal_zero_succ K q n h) x

end

end OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexDifferential.DoubleComplex

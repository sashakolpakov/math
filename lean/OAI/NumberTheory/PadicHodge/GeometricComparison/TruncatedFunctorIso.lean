import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD

/-! # Truncated Functor Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TruncatedFunctorIso.TruncatedPullback

noncomputable section

section

/-! A morphism of complexes across an additive functor restricts to every degree truncation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive]

omit [HasZeroObject C] [HasZeroObject D] in
theorem zero_square {A B : C} {Y Z : D} (u : Y ⟶ Z) (v : F.obj B ⟶ Z) :
    (0 : F.obj A ⟶ Y) ≫ u = F.map (0 : A ⟶ B) ≫ v := by
  rw [F.map_zero, zero_comp, zero_comp]

omit [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D] [F.Additive] in
theorem transport_square {A A' B B' : C} {Y Y' Z Z' : D}
    (hA : A' = A) (hB : B' = B) (hY : Y' = Y) (hZ : Z' = Z)
    (a : F.obj A ⟶ Y) (b : F.obj B ⟶ Z) (u : A ⟶ B) (v : Y ⟶ Z)
    (h : a ≫ v = F.map u ≫ b) :
    (eqToHom (congrArg F.obj hA) ≫ a ≫ eqToHom hY.symm) ≫
        (eqToHom hY ≫ v ≫ eqToHom hZ.symm) =
      F.map (eqToHom hA ≫ u ≫ eqToHom hB.symm) ≫
        (eqToHom (congrArg F.obj hB) ≫ b ≫ eqToHom hZ.symm) := by
  cases hA
  cases hB
  cases hY
  cases hZ
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

omit [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D] [F.Additive] in
theorem transport_inclusion {A A' : C} {Y Y' : D}
    (hA : A' = A) (hY : Y' = Y) (a : F.obj A ⟶ Y) :
    (eqToHom (congrArg F.obj hA) ≫ a ≫ eqToHom hY.symm) ≫ eqToHom hY =
      F.map (eqToHom hA) ≫ a := by
  cases hA
  cases hY
  simp only [eqToHom_refl, F.map_id, Category.id_comp, Category.comp_id]

variable
  {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (f : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ L)

def component (r : ℤ) (n : ℕ) : F.obj (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K r n) ⟶ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term L r n :=
  if h : r ≤ (n : ℤ) then
    eqToHom (by simp [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, h]) ≫ f.f n ≫ eqToHom (by simp [AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, h])
  else 0

def map (r : ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r) ⟶ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r where
  f n := component F f r n
  comm' n m hnm := by
    obtain rfl := (show n + 1 = m from hnm)
    change component F f r n ≫ (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r).d n (n + 1) =
      F.map ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r).d n (n + 1)) ≫ component F f r (n + 1)
    rw [show (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r).d n (n + 1) = AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.d K r n from CochainComplex.of_d _ _ n,
      show (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r).d n (n + 1) = AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.d L r n from CochainComplex.of_d _ _ n]
    by_cases h : r ≤ (n : ℤ)
    · have h1 : r ≤ ((n + 1 : ℕ) : ℤ) := by omega
      simp only [component, AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.d, dite_eq_left h, dite_eq_left h1]
      exact transport_square F (show AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K r n = K.X n from ite_eq_left h)
        (show AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K r (n + 1) = K.X (n + 1) from ite_eq_left h1)
        (show AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term L r n = L.X n from ite_eq_left h)
        (show AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term L r (n + 1) = L.X (n + 1) from ite_eq_left h1)
        (f.f n) (f.f (n + 1)) (K.d n (n + 1)) (L.d n (n + 1)) (f.comm n (n + 1))
    · simp only [component, AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.d, dite_eq_right h]
      exact zero_square F _ _

theorem inclusion_square (r : ℤ) :
    TruncatedPullback.map F f r ≫ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r =
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) ≫ f := by
  apply HomologicalComplex.Hom.ext
  funext n
  change component F f r n ≫ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm L r n = F.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K r n) ≫ f.f n
  by_cases h : r ≤ (n : ℤ)
  · simp only [component, AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_left h]
    exact transport_inclusion F (show AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K r n = K.X n from ite_eq_left h)
      (show AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term L r n = L.X n from ite_eq_left h) (f.f n)
  · simp only [component, AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_right h]
    exact zero_square F _ _

end

/-! An additive functor preserves the actual Hodge truncation through the canonical component map. -/

open _root_.CategoryTheory Limits ZeroObject OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive]
  {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (e : (F.mapHomologicalComplex (.up ℕ)).obj K ≅ L)

theorem component_isIso (r : ℤ) (n : ℕ) : IsIso (component F e.hom r n) := by
  by_cases h : r ≤ (n : ℤ)
  · dsimp only [component]
    rw [dite_eq_left h]
    infer_instance
  · have hK : IsZero (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K r n) := (isZero_zero C).of_iso (eqToIso (ite_eq_right h))
    have hL : IsZero (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term L r n) := (isZero_zero D).of_iso (eqToIso (ite_eq_right h))
    exact (F.map_isZero hK).isIso hL (component F e.hom r n)

def iso (r : ℤ) : (F.mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r) ≅ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r := by
  have : ∀ n, IsIso ((TruncatedPullback.map F e.hom r).f n) := fun n => component_isIso F e r n
  have : IsIso (TruncatedPullback.map F e.hom r) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (TruncatedPullback.map F e.hom r)

theorem iso_inclusion (r : ℤ) :
    (iso F e r).hom ≫ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r =
      (F.mapHomologicalComplex (.up ℕ)).map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) ≫ e.hom :=
  inclusion_square F e.hom r

theorem iso_inv_inclusion (r : ℤ) :
    (iso F e r).inv ≫ (F.mapHomologicalComplex (.up ℕ)).map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) =
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r ≫ e.inv := by
  apply (iso F e r).inv_comp_eq.mpr
  have h := congrArg (fun f => f ≫ e.inv) (iso_inclusion F e r)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TruncatedFunctorIso.TruncatedPullback

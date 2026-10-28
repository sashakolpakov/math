import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD

/-! # Brutal Complex Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.BrutalComplexMap.Hodge

noncomputable section

section

/-! The independently defined degree truncation retains actual cochain morphisms and their inclusions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  {K L : CochainComplex C ℕ} (φ : K ⟶ L) (r : ℤ)

def brutalTermMap (n : ℕ) : Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K r n ⟶ Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term L r n :=
  if h : r ≤ (n : ℤ) then
    eqToHom (by simp only [Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, ite_eq_left h]) ≫ φ.f n ≫ eqToHom (by simp only [Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, ite_eq_left h])
  else 0

def brutalComplexMap : Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r ⟶ Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r where
  f := brutalTermMap φ r
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    rw [show (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r).d n (n + 1) = Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.d K r n from CochainComplex.of_d _ _ n,
      show (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r).d n (n + 1) = Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.d L r n from CochainComplex.of_d _ _ n]
    change brutalTermMap φ r n ≫ Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.d L r n = Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.d K r n ≫ brutalTermMap φ r (n + 1)
    by_cases h : r ≤ (n : ℤ)
    · have h' : r ≤ ((n + 1 : ℕ) : ℤ) := by omega
      simp only [brutalTermMap, Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.d, dite_eq_left h, dite_eq_left h', Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [φ.comm_assoc]
    · simp only [brutalTermMap, Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.d, dite_eq_right h, comp_zero, zero_comp]

theorem brutalComplexMap_inclusion :
    brutalComplexMap φ r ≫ Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r = Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r ≫ φ := by
  apply HomologicalComplex.Hom.ext
  funext n
  change brutalTermMap φ r n ≫ Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm L r n = Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K r n ≫ φ.f n
  by_cases h : r ≤ (n : ℤ)
  · simp only [brutalTermMap, Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_left h, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.comp_id]
  · simp only [brutalTermMap, Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_right h, comp_zero, zero_comp]

end

/-! The retained and zero terms of the independent Hodge truncation have canonical identifications. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits ZeroObject

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  (K : CochainComplex C ℕ) (r : ℤ) (n : ℕ)

def brutalRetainedTermIso (h : r ≤ (n : ℤ)) : Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K r n ≅ K.X n :=
  eqToIso (by simp only [Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, ite_eq_left h])

theorem brutalRetainedTermIso_inclusion (h : r ≤ (n : ℤ)) :
    (brutalRetainedTermIso K r n h).hom = Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K r n := by
  simp only [brutalRetainedTermIso, Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_left h, eqToIso.hom]

theorem brutalTerm_isZero (h : ¬ r ≤ (n : ℤ)) : IsZero (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K r n) := by
  have he : Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term K r n = 0 := by simp only [Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.term, ite_eq_right h]
  exact IsZero.of_iso (isZero_zero C) (eqToIso he)

theorem brutalInclusionTerm_mono : Mono (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusionTerm K r n) := by
  by_cases h : r ≤ (n : ℤ)
  · rw [← brutalRetainedTermIso_inclusion K r n h]
    infer_instance
  · exact (brutalTerm_isZero K r n h).mono _

end

end OAI.AlgebraicGeometry.Comparison.Betti.BrutalComplexMap.Hodge

import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId
import Lean.Elab.Tactic.Omega

/-! # Hodge Filtration D -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

noncomputable section

/-!
# Cohomology: the Hodge filtration on algebraic de Rham hypercohomology

The filtration is the image of the degree truncation of the de Rham complex.
The maps between truncations, their factorization through the full complex,
and the decreasing property on hypercohomology are proved explicitly.
-/

open _root_.CategoryTheory Limits ZeroObject _root_.AlgebraicGeometry

universe u v

section Truncation

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
variable (K : CochainComplex C ℕ)

def term (r : ℤ) (n : ℕ) : C := if r ≤ (n : ℤ) then K.X n else 0

def d (r : ℤ) (n : ℕ) : term K r n ⟶ term K r (n + 1) :=
  if h : r ≤ (n : ℤ) then
    eqToHom (by simp [term, h]) ≫ K.d n (n + 1) ≫
      eqToHom (by
        have h' : r ≤ ((n + 1 : ℕ) : ℤ) := by omega
        simp only [term, ite_eq_left h'])
  else 0

theorem d_square (r : ℤ) (n : ℕ) : HodgeFiltration.d K r n ≫ HodgeFiltration.d K r (n + 1) = 0 := by
  by_cases h : r ≤ (n : ℤ)
  · have h1 : r ≤ ((n + 1 : ℕ) : ℤ) := by omega
    simp only [HodgeFiltration.d, dite_eq_left h, dite_eq_left h1, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp, HomologicalComplex.d_comp_d_assoc, zero_comp,
      comp_zero]
  · simp only [HodgeFiltration.d, dite_eq_right h, zero_comp]

/-- Retain degrees at or above the specified integer. -/
def brutal (r : ℤ) : CochainComplex C ℕ :=
  CochainComplex.of (term K r) (HodgeFiltration.d K r) (d_square K r)

def inclusionTerm (r : ℤ) (n : ℕ) : term K r n ⟶ K.X n :=
  if h : r ≤ (n : ℤ) then eqToHom (by simp [term, h]) else 0

/-- The canonical inclusion of the degree truncation. -/
def inclusion (r : ℤ) : brutal K r ⟶ K where
  f n := inclusionTerm K r n
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    rw [show (brutal K r).d n (n + 1) = HodgeFiltration.d K r n from CochainComplex.of_d _ _ n]
    change inclusionTerm K r n ≫ K.d n (n + 1) = HodgeFiltration.d K r n ≫ inclusionTerm K r (n + 1)
    by_cases h : r ≤ (n : ℤ)
    · have h1 : r ≤ ((n + 1 : ℕ) : ℤ) := by omega
      simp only [inclusionTerm, HodgeFiltration.d, dite_eq_left h, dite_eq_left h1, Category.assoc,
        eqToHom_trans, eqToHom_refl, Category.comp_id]
    · simp only [inclusionTerm, HodgeFiltration.d, dite_eq_right h, zero_comp]

def transitionTerm {r s : ℤ} (hrs : r ≤ s) (n : ℕ) : term K s n ⟶ term K r n :=
  if h : s ≤ (n : ℤ) then eqToHom (by simp [term, h, hrs.trans h]) else 0

/-- A higher degree cutoff includes in every lower cutoff. -/
def transition {r s : ℤ} (hrs : r ≤ s) : brutal K s ⟶ brutal K r where
  f n := transitionTerm K hrs n
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    rw [show (brutal K r).d n (n + 1) = HodgeFiltration.d K r n from CochainComplex.of_d _ _ n,
      show (brutal K s).d n (n + 1) = HodgeFiltration.d K s n from CochainComplex.of_d _ _ n]
    change transitionTerm K hrs n ≫ HodgeFiltration.d K r n = HodgeFiltration.d K s n ≫ transitionTerm K hrs (n + 1)
    by_cases h : s ≤ (n : ℤ)
    · have h1 : s ≤ ((n + 1 : ℕ) : ℤ) := by omega
      simp only [transitionTerm, HodgeFiltration.d, dite_eq_left h, dite_eq_left h1, dite_eq_left (hrs.trans h),
        Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    · simp only [transitionTerm, HodgeFiltration.d, dite_eq_right h, zero_comp]

theorem transition_inclusion {r s : ℤ} (hrs : r ≤ s) :
    transition K hrs ≫ inclusion K r = inclusion K s := by
  ext n
  change transitionTerm K hrs n ≫ inclusionTerm K r n = inclusionTerm K s n
  by_cases h : s ≤ (n : ℤ)
  · simp only [transitionTerm,
      inclusionTerm, dite_eq_left h, dite_eq_left (hrs.trans h), eqToHom_trans]
  · simp only [transitionTerm,
      inclusionTerm, dite_eq_right h, zero_comp]

end Truncation

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

abbrev Sheaves := DeRhamGlobalId.DeRhamGlobal.Sheaves R X

/-- Pass a nonnegative sheaf complex to the derived category by extending by zero. -/
def derivedFunctor : CochainComplex (Sheaves R X) ℕ ⥤ DerivedCategory (Sheaves R X) :=
  ComplexShape.embeddingUpNat.extendFunctor (Sheaves R X) ⋙ DerivedCategory.Q

def filtrationMap (n : ℕ) (r : ℤ) :
    ShiftedHom ((DerivedCategory.singleFunctor (Sheaves R X) 0).obj
      (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X))
      ((derivedFunctor R X).obj (brutal (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r)) (n : ℤ)
      →ₗ[R] DeRhamGlobalId.DeRhamGlobal.cohomology R X n :=
  Linear.rightComp R _ ((shiftFunctor (DerivedCategory (Sheaves R X)) (n : ℤ)).map
    ((derivedFunctor R X).map (inclusion (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r)))

/-- The Hodge filtration is the image of the truncated de Rham complex. -/
def filtration (n : ℕ) (r : ℤ) : Submodule R (DeRhamGlobalId.DeRhamGlobal.cohomology R X n) :=
  LinearMap.range (filtrationMap R X n r)

theorem filtration_antitone (n : ℕ) : Antitone (filtration R X n) := by
  intro r s hrs z hz
  obtain ⟨y, rfl⟩ := hz
  refine ⟨y ≫ (shiftFunctor (DerivedCategory (Sheaves R X)) (n : ℤ)).map
    ((derivedFunctor R X).map (transition (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) hrs)), ?_⟩
  change (y ≫ (shiftFunctor (DerivedCategory (Sheaves R X)) (n : ℤ)).map
      ((derivedFunctor R X).map (transition (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) hrs))) ≫
    (shiftFunctor (DerivedCategory (Sheaves R X)) (n : ℤ)).map
      ((derivedFunctor R X).map (inclusion (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r)) =
    y ≫ (shiftFunctor (DerivedCategory (Sheaves R X)) (n : ℤ)).map
      ((derivedFunctor R X).map (inclusion (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) s))
  rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, transition_inclusion]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

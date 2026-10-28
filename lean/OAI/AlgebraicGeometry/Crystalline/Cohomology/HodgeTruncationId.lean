import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD

/-! # Hodge Truncation Id -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeTruncationId.HodgeTruncationFunctor

noncomputable section

/-!
# Functorial degree truncation for the native Hodge filtration

Every cochain map induces a map on the exact degree truncations used by
Cohomology. The inclusions commute with these maps, and truncation preserves
identities and composition.
-/

open _root_.CategoryTheory Limits

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {K L M : CochainComplex C ℕ}

def mapTerm (f : K ⟶ L) (r : ℤ) (n : ℕ) : HodgeFiltrationD.HodgeFiltration.term K r n ⟶ HodgeFiltrationD.HodgeFiltration.term L r n :=
  if h : r ≤ (n : ℤ) then
    eqToHom (by simp [HodgeFiltrationD.HodgeFiltration.term, h]) ≫ f.f n ≫
      eqToHom (by simp [HodgeFiltrationD.HodgeFiltration.term, h])
  else 0

def map (f : K ⟶ L) (r : ℤ) : HodgeFiltrationD.HodgeFiltration.brutal K r ⟶ HodgeFiltrationD.HodgeFiltration.brutal L r where
  f n := mapTerm f r n
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    rw [show (HodgeFiltrationD.HodgeFiltration.brutal K r).d n (n + 1) = HodgeFiltrationD.HodgeFiltration.d K r n from CochainComplex.of_d _ _ n,
      show (HodgeFiltrationD.HodgeFiltration.brutal L r).d n (n + 1) = HodgeFiltrationD.HodgeFiltration.d L r n from CochainComplex.of_d _ _ n]
    change mapTerm f r n ≫ HodgeFiltrationD.HodgeFiltration.d L r n = HodgeFiltrationD.HodgeFiltration.d K r n ≫ mapTerm f r (n + 1)
    by_cases h : r ≤ (n : ℤ)
    · have h1 : r ≤ ((n + 1 : ℕ) : ℤ) := by omega
      simp only [mapTerm, HodgeFiltrationD.HodgeFiltration.d, dite_eq_left h, dite_eq_left h1, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, f.comm_assoc]
    · simp only [mapTerm, HodgeFiltrationD.HodgeFiltration.d, dite_eq_right h, zero_comp]

/-- The truncation inclusion is natural for every cochain map. -/
theorem map_inclusion (f : K ⟶ L) (r : ℤ) :
    HodgeTruncationFunctor.map f r ≫ HodgeFiltrationD.HodgeFiltration.inclusion L r = HodgeFiltrationD.HodgeFiltration.inclusion K r ≫ f := by
  ext n
  change mapTerm f r n ≫ HodgeFiltrationD.HodgeFiltration.inclusionTerm L r n = HodgeFiltrationD.HodgeFiltration.inclusionTerm K r n ≫ f.f n
  by_cases h : r ≤ (n : ℤ)
  · simp only [mapTerm, HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_left h, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.comp_id]
  · simp only [mapTerm, HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_right h, zero_comp]

theorem map_id (K : CochainComplex C ℕ) (r : ℤ) : HodgeTruncationFunctor.map (𝟙 K) r = 𝟙 (HodgeFiltrationD.HodgeFiltration.brutal K r) := by
  ext n
  by_cases h : r ≤ (n : ℤ)
  · change mapTerm (𝟙 K) r n = 𝟙 _
    simp only [mapTerm, dite_eq_left h, HomologicalComplex.id_f, Category.id_comp,
      eqToHom_trans, eqToHom_refl]
  · change mapTerm (𝟙 K) r n = 𝟙 (HodgeFiltrationD.HodgeFiltration.term K r n)
    rw [mapTerm, dite_eq_right h]
    exact (by
      have hz : IsZero (HodgeFiltrationD.HodgeFiltration.term K r n) := by
        simpa only [HodgeFiltrationD.HodgeFiltration.term, ite_eq_right h] using (isZero_zero C)
      exact hz.eq_of_src _ _)

theorem map_comp (f : K ⟶ L) (g : L ⟶ M) (r : ℤ) : HodgeTruncationFunctor.map (f ≫ g) r = HodgeTruncationFunctor.map f r ≫ HodgeTruncationFunctor.map g r := by
  ext n
  change mapTerm (f ≫ g) r n = mapTerm f r n ≫ mapTerm g r n
  by_cases h : r ≤ (n : ℤ)
  · simp only [mapTerm, dite_eq_left h, HomologicalComplex.comp_f, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  · simp only [mapTerm, dite_eq_right h, zero_comp]

def functor (r : ℤ) : CochainComplex C ℕ ⥤ CochainComplex C ℕ where
  obj K := HodgeFiltrationD.HodgeFiltration.brutal K r
  map f := HodgeTruncationFunctor.map f r
  map_id K := HodgeTruncationFunctor.map_id K r
  map_comp f g := HodgeTruncationFunctor.map_comp f g r

def inclusion (r : ℤ) : functor (C := C) r ⟶ 𝟭 (CochainComplex C ℕ) where
  app K := HodgeFiltrationD.HodgeFiltration.inclusion K r
  naturality _ _ f := map_inclusion f r

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeTruncationId.HodgeTruncationFunctor

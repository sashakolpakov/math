import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeTruncationId

/-! # Hodge Truncation Term -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeTruncationTerm.HodgeTruncationFactor

noncomputable section

/-!
# Factoring cochain maps through the native Hodge truncation

A complex that vanishes below a degree cutoff maps canonically into the
same cutoff of any target. In particular, an additive image of a native
Hodge truncation factors through the target truncation. This supplies
the truncated pullback map without choosing any cohomological data.
-/

open _root_.CategoryTheory Limits

universe u v w z

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {K L : CochainComplex C ℕ} (g : K ⟶ L) (r : ℤ)

def term (n : ℕ) : K.X n ⟶ HodgeFiltrationD.HodgeFiltration.term L r n :=
  if h : r ≤ (n : ℤ) then g.f n ≫ eqToHom (by simp [HodgeFiltrationD.HodgeFiltration.term, h]) else 0

variable (hzero : ∀ n : ℕ, ¬ r ≤ (n : ℤ) → IsZero (K.X n))

def factor : K ⟶ HodgeFiltrationD.HodgeFiltration.brutal L r where
  f n := term g r n
  comm' n m hnm := by
    change n + 1 = m at hnm
    subst m
    rw [show (HodgeFiltrationD.HodgeFiltration.brutal L r).d n (n + 1) = HodgeFiltrationD.HodgeFiltration.d L r n from CochainComplex.of_d _ _ n]
    change term g r n ≫ HodgeFiltrationD.HodgeFiltration.d L r n = K.d n (n + 1) ≫ term g r (n + 1)
    by_cases h : r ≤ (n : ℤ)
    · have h1 : r ≤ ((n + 1 : ℕ) : ℤ) := by omega
      simp only [term, HodgeFiltrationD.HodgeFiltration.d, dite_eq_left h, dite_eq_left h1, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, g.comm_assoc]
    · exact (hzero n h).eq_of_src _ _

theorem factor_inclusion : factor g r hzero ≫ HodgeFiltrationD.HodgeFiltration.inclusion L r = g := by
  ext n
  change term g r n ≫ HodgeFiltrationD.HodgeFiltration.inclusionTerm L r n = g.f n
  by_cases h : r ≤ (n : ℤ)
  · simp only [term, HodgeFiltrationD.HodgeFiltration.inclusionTerm, dite_eq_left h, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.comp_id]
  · exact (hzero n h).eq_of_src _ _

variable {D : Type w} [Category.{z} D] [HasZeroMorphisms D] [HasZeroObject D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] (M : CochainComplex C ℕ)

omit [HasZeroObject D] in
theorem mapped_zero_below (n : ℕ) (hn : ¬ r ≤ (n : ℤ)) :
    IsZero (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (HodgeFiltrationD.HodgeFiltration.brutal M r)).X n) := by
  apply F.map_isZero
  change IsZero (HodgeFiltrationD.HodgeFiltration.term M r n)
  rw [HodgeFiltrationD.HodgeFiltration.term, ite_eq_right hn]
  exact isZero_zero C

variable {N : CochainComplex D ℕ} (f : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj M ⟶ N)

/-- A canonical truncated map for every cochain map out of the additive image. -/
def mappedFactor : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (HodgeFiltrationD.HodgeFiltration.brutal M r) ⟶
    HodgeFiltrationD.HodgeFiltration.brutal N r :=
  factor ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (HodgeFiltrationD.HodgeFiltration.inclusion M r) ≫ f)
    r (mapped_zero_below r F M)

theorem mappedFactor_inclusion : mappedFactor r F M f ≫ HodgeFiltrationD.HodgeFiltration.inclusion N r =
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (HodgeFiltrationD.HodgeFiltration.inclusion M r) ≫ f :=
  factor_inclusion _ r _

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeTruncationTerm.HodgeTruncationFactor

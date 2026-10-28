import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale

/-! # Multiplication -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction

noncomputable section

/-! Actual multiplication covers and torsion schemes for the endomorphism argument. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K : Type u} [Field K]

/-- An integer nonzero in the field is a unit in every actual base stalk. -/
theorem field_natCast_stalk_isUnit (n : ℕ) (hn : (n : K) ≠ 0)
    (x : Spec (CommRingCat.of K)) :
    IsUnit (n : (Spec (CommRingCat.of K)).presheaf.stalk x) := by
  let φ := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
    (Spec (CommRingCat.of K)).presheaf.germ ⊤ x trivial).hom
  simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hn).map φ

variable (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]

/-- Addition in the genuine endomorphism ring is the actual pointwise group law. -/
theorem algebraicEnd_nsmul_hom (n : ℕ) (f : Endomorphisms.Construction.AlgebraicEnd A) :
    (n • f).toMul.hom.hom = f.toMul.hom.hom ^ n := by
  change (f.toMul ^ n).hom.hom = _
  simp only [Grp.Hom.hom_pow, Mon.Hom.hom_pow]

/-- Multiplication by n is a homomorphism of the actual commutative group scheme. -/
instance multiplication_isMonHom (n : ℕ) : IsMonHom ((𝟙 A : A ⟶ A) ^ n) := by
  have h : (n • (1 : Endomorphisms.Construction.AlgebraicEnd A)).toMul.hom.hom = (𝟙 A : A ⟶ A) ^ n :=
    algebraicEnd_nsmul_hom A n 1
  rw [← h]
  infer_instance

/-- The actual multiplication morphism is finite when the integer is nonzero in the base field. -/
theorem multiplication_isFinite [IsProper A.hom] (n : ℕ) (hn : (n : K) ≠ 0) :
    IsFinite ((𝟙 A : A ⟶ A) ^ n).left := by
  have : IsProper ((𝟙 A : A ⟶ A) ^ n).left := AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.power_isProper A n
  have : FormallyUnramified ((𝟙 A : A ⟶ A) ^ n).left :=
    AbelianScheme.TorsionQuotient.Power.PowerGeometry.power_formallyUnramified A n (field_natCast_stalk_isUnit n hn)
  exact AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.finite_of_proper_formallyUnramified _

/-- Etaleness is derived from the actual infinitesimal lifting calculation. -/
theorem multiplication_etale [Smooth A.hom] (n : ℕ) (hn : (n : K) ≠ 0) :
    Etale ((𝟙 A : A ⟶ A) ^ n).left :=
  AbelianScheme.TorsionQuotient.Etale.TorsionEtale.power_etale A n (field_natCast_stalk_isUnit n hn)

/-- Connectedness makes the nonempty clopen image of multiplication the whole scheme. -/
theorem multiplication_surjective_of_connected [IsProper A.hom] [Smooth A.hom]
    [PreconnectedSpace A.left] [Nonempty A.left] (n : ℕ) (hn : (n : K) ≠ 0) :
    Surjective ((𝟙 A : A ⟶ A) ^ n).left := by
  have : IsFinite ((𝟙 A : A ⟶ A) ^ n).left := multiplication_isFinite A n hn
  have : Etale ((𝟙 A : A ⟶ A) ^ n).left := multiplication_etale A n hn
  let f := ((𝟙 A : A ⟶ A) ^ n).left
  have hc : IsClopen (Set.range f) := ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩
  exact ⟨Set.range_eq_univ.mp (hc.eq_univ (Set.range_nonempty f))⟩

/-- The actual finite etale multiplication cover of a geometrically integral group is surjective. -/
theorem multiplication_surjective [IsProper A.hom] [Smooth A.hom]
    [GeometricallyIntegral A.hom] (n : ℕ) (hn : (n : K) ≠ 0) :
    Surjective ((𝟙 A : A ⟶ A) ^ n).left := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  exact multiplication_surjective_of_connected A n hn

/-- The actual equalizer of multiplication and zero is finite etale over the field. -/
theorem torsionScheme_finite_etale [IsProper A.hom] [Smooth A.hom]
    (n : ℕ) (hn : (n : K) ≠ 0) :
    IsFinite (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom ∧ Etale (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom :=
  AbelianScheme.TorsionQuotient.Etale.TorsionEtale.torsion_finite_etale A n (field_natCast_stalk_isUnit n hn)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction

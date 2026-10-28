import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.GroupDivisionLocus

/-! # Group Division Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.GroupDivisionLocus

noncomputable section

/-! The closed locus for division of an abelian-scheme homomorphism by
an integer invertible on the base. The universal property includes every
test scheme and does not require a level structure at that integer. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem unit_multiplication_geometry
    {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
    (n : ℕ) (hnUnit : IsUnit (n : Γ(S, ⊤))) :
    IsFinite (A.multiplication n).left ∧ Flat (A.multiplication n).left ∧
      Surjective (A.multiplication n).left ∧
      LocallyOfFinitePresentation (A.multiplication n).left ∧
      Etale (A.multiplication n).left := by
  have hstalk (x : S) : IsUnit (n : S.presheaf.stalk x) := by
    simpa only [map_natCast] using
      hnUnit.map (S.presheaf.germ ⊤ x (by trivial)).hom
  exact AbelianScheme.IsogenyQuotient.Multiplication.Construction.multiplication_geometry_from_TorsionQuotient A.scheme n
    (AbelianScheme.TorsionQuotient.Etale.TorsionEtale.torsion_finite_etale A.scheme n hstalk)

theorem unit_group_division_closed_locus
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    {g h : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (n : ℕ) (hnUnit : IsUnit (n : Γ(S, ⊤)))
    (m : A.scheme ⟶ B.scheme) [IsMonHom m] :
    ∃ (Z : Over S) (j : Z ⟶ Over.mk (𝟙 S)), IsClosedImmersion j.left ∧
      ∀ T : Over S,
        (∃! p : {f : (A.pullback T.hom).scheme ⟶ (B.pullback T.hom).scheme // IsMonHom f},
          (A.pullback T.hom).multiplication n ≫ p.val = (Over.pullback T.hom).map m) ↔
        ∃! y : T ⟶ Z, y ≫ j = Over.mkIdTerminal.from T := by
  have hg := unit_multiplication_geometry A n hnUnit
  let : IsFinite (A.multiplication n).left := hg.1
  let : Flat (A.multiplication n).left := hg.2.1
  let : IsFinite (A.torsionScheme n).hom :=
    inferInstanceAs (IsFinite (pullback.snd (A.multiplication n).left η[A.scheme].left))
  let : Flat (A.torsionScheme n).hom :=
    inferInstanceAs (Flat (pullback.snd (A.multiplication n).left η[A.scheme].left))
  obtain ⟨Z, j, hj, ht⟩ := ProperFlat.MorphismEqualityLocus.proper_flat_morphism_equality_closed_locus
    (A.torsionInclusion n ≫ m) (1 : A.torsionScheme n ⟶ B.scheme)
  refine ⟨Z, j, hj, ?_⟩
  intro T
  have hgT := unit_multiplication_geometry (A.pullback T.hom) n
    (Abelian.Schemes.level_unit_under_base_change T.hom n hnUnit)
  let : IsFinite ((A.pullback T.hom).multiplication n).left := hgT.1
  let : Flat ((A.pullback T.hom).multiplication n).left := hgT.2.1
  let : Surjective ((A.pullback T.hom).multiplication n).left := hgT.2.2.1
  let : IsMonHom (show (A.pullback T.hom).scheme ⟶ (B.pullback T.hom).scheme from
      (Over.pullback T.hom).map m) :=
    Functor.map.instIsMonHom (F := Over.pullback T.hom) (f := m) A.scheme B.scheme
  have htest : (Over.pullback T.hom).map (A.torsionInclusion n ≫ m) = 1 ↔
      ∃! y : T ⟶ Z, y ≫ j = Over.mkIdTerminal.from T := by
    simpa only [Functor.map_one] using ht T
  exact
    (Rational.GroupDivisionLocus.torsion_killed_iff_unique_group_division (A.pullback T.hom) (B.pullback T.hom)
      n ((Over.pullback T.hom).map m)).symm.trans
      ((Rational.GroupDivisionLocus.kills_torsion_baseChange_iff A B T.hom n m).symm.trans htest)

theorem unit_divisor_finite_etale
    {S : Scheme.{u}} {g h : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (n : ℕ) (hnUnit : IsUnit (n : Γ(S, ⊤))) (m p : A.scheme ⟶ B.scheme)
    [IsFinite m.left] [Etale m.left] [Surjective m.left] [IsMonHom p]
    (hp : A.multiplication n ≫ p = m) :
    IsFinite p.left ∧ Etale p.left ∧ Surjective p.left := by
  have hscalar : A.multiplication n ≫ p = p ^ n := by
    change ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n) ≫ p = p ^ n
    rw [MonObj.pow_comp, Category.id_comp]
  have he : p ≫ B.multiplication n = m :=
    (B.comp_multiplication n p).trans (hscalar.symm.trans hp)
  let : Etale (B.multiplication n).left :=
    (unit_multiplication_geometry B n hnUnit).2.2.2.2
  let : IsFinite (p.left ≫ (B.multiplication n).left) := by
    change IsFinite (p ≫ B.multiplication n).left
    rw [he]
    infer_instance
  let : Etale (p.left ≫ (B.multiplication n).left) := by
    change Etale (p ≫ B.multiplication n).left
    rw [he]
    infer_instance
  let : Surjective ((A.multiplication n).left ≫ p.left) := by
    change Surjective (A.multiplication n ≫ p).left
    rw [hp]
    infer_instance
  exact ⟨IsFinite.of_comp p.left (B.multiplication n).left,
    Etale.of_comp p.left (B.multiplication n).left,
    Surjective.of_comp (A.multiplication n).left p.left⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.GroupDivisionLocus

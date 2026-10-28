import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.MorphismEqualityLocus
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GroupDivisionOverBase
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TorsionBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Multiplication
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale

/-! # Group Division Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.GroupDivisionLocus

noncomputable section

/-! The actual closed locus on which a homomorphism is divisible by a
positive integer. Division is unique on every test scheme; no level
structure at the dividing integer is required. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem rational_multiplication_geometry
    {S : Scheme} (qS : S ⟶ Spec (.of ℚ)) {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (n : ℕ) (hn : 0 < n) :
    IsFinite (A.multiplication n).left ∧ Flat (A.multiplication n).left ∧
      Surjective (A.multiplication n).left ∧
      LocallyOfFinitePresentation (A.multiplication n).left ∧
      Etale (A.multiplication n).left :=
  AbelianScheme.IsogenyQuotient.Multiplication.Construction.multiplication_geometry_from_TorsionQuotient A.scheme n
    (AbelianScheme.TorsionQuotient.Etale.TorsionEtale.torsion_finite_etale A.scheme n
      (AbelianScheme.IsogenyQuotient.Unit.Construction.positive_integer_unit_on_characteristic_zero_base qS n hn))

theorem torsion_killed_iff_unique_group_division
    {S : Scheme.{u}} {g h : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (n : ℕ) (m : A.scheme ⟶ B.scheme) [IsMonHom m]
    [IsFinite (A.multiplication n).left] [Flat (A.multiplication n).left]
    [Surjective (A.multiplication n).left] :
    A.torsionInclusion n ≫ m = 1 ↔
      ∃! p : {f : A.scheme ⟶ B.scheme // IsMonHom f}, A.multiplication n ≫ p.val = m := by
  let : IsMonHom (A.multiplication n) := by
    rw [← A.endRing_natCast_hom n]
    infer_instance
  let : EffectiveEpi (A.multiplication n).left := inferInstance
  let : Epi (A.multiplication n ⊗ₘ A.multiplication n) :=
    FaithfullyFlatTensorEpi.over_tensor_epi_of_flat_surjective (A.multiplication n) (A.multiplication n)
  constructor
  · intro hm
    obtain ⟨p, hp, hu⟩ := HilbertConstruction.Over.EffectiveDescent.over_existsUnique_factor_of_effectiveEpi (A.multiplication n) m
      (fun a b hab => A.torsion_annihilator_relation B m hm a b hab)
    refine ⟨⟨p, MonoidHomEpiDescent.isMonHom_of_tensor_epi (A.multiplication n) m p hp⟩, hp, ?_⟩
    intro z hz
    exact Subtype.ext (hu z.val hz)
  · rintro ⟨p, hp, _⟩
    let : IsMonHom p.val := p.property
    rw [← hp, ← Category.assoc, A.comp_multiplication,
      A.torsionInclusion_pow, MonObj.one_comp]

theorem kills_torsion_baseChange_iff
    {S T : Scheme.{u}} {g h : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (b : T ⟶ S) (n : ℕ) (m : A.scheme ⟶ B.scheme) :
    (Over.pullback b).map (A.torsionInclusion n ≫ m) = 1 ↔
      (A.pullback b).torsionInclusion n ≫ (Over.pullback b).map m = 1 := by
  let e := AbelianScheme.FrobeniusKernel.TorsionBaseChange.Construction.torsionSchemeBaseChangeIso A b n
  have he : e.hom ≫ (A.pullback b).torsionInclusion n =
      (Over.pullback b).map (A.torsionInclusion n) :=
    AbelianScheme.FrobeniusKernel.TorsionBaseChange.Construction.torsionSchemeBaseChangeIso_inclusion A b n
  let mb : (A.pullback b).scheme ⟶ (Over.pullback b).obj B.scheme := (Over.pullback b).map m
  have hm : (Over.pullback b).map (A.torsionInclusion n ≫ m) =
      e.hom ≫ ((A.pullback b).torsionInclusion n ≫ mb) :=
    ((Over.pullback b).map_comp (A.torsionInclusion n) m).trans
      ((congrArg (fun k : (Over.pullback b).obj (A.torsionScheme n) ⟶ (A.pullback b).scheme =>
        k ≫ mb) he.symm).trans (Category.assoc _ _ _))
  rw [hm]
  have hc :
      e.hom ≫ ((A.pullback b).torsionInclusion n ≫ (Over.pullback b).map m) =
        e.hom ≫ (1 : (A.pullback b).torsionScheme n ⟶ (Over.pullback b).obj B.scheme) ↔
      (A.pullback b).torsionInclusion n ≫ (Over.pullback b).map m = 1 :=
    cancel_epi e.hom
  simpa only [mb, MonObj.comp_one] using hc

theorem rational_group_division_closed_locus
    {S : Scheme} [IsLocallyNoetherian S] (qS : S ⟶ Spec (.of ℚ))
    {g h : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (n : ℕ) (hn : 0 < n) (m : A.scheme ⟶ B.scheme) [IsMonHom m] :
    ∃ (Z : Over S) (j : Z ⟶ Over.mk (𝟙 S)), IsClosedImmersion j.left ∧
      ∀ T : Over S,
        (∃! p : {f : (A.pullback T.hom).scheme ⟶ (B.pullback T.hom).scheme // IsMonHom f},
          (A.pullback T.hom).multiplication n ≫ p.val = (Over.pullback T.hom).map m) ↔
        ∃! y : T ⟶ Z, y ≫ j = Over.mkIdTerminal.from T := by
  have hg := rational_multiplication_geometry qS A n hn
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
  have hgT := rational_multiplication_geometry (T.hom ≫ qS) (A.pullback T.hom) n hn
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
    (torsion_killed_iff_unique_group_division (A.pullback T.hom) (B.pullback T.hom)
      n ((Over.pullback T.hom).map m)).symm.trans
      ((kills_torsion_baseChange_iff A B T.hom n m).symm.trans htest)

theorem rational_divisor_finite_etale
    {S : Scheme} (qS : S ⟶ Spec (.of ℚ)) {g h : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (n : ℕ) (hn : 0 < n) (m p : A.scheme ⟶ B.scheme)
    [IsFinite m.left] [Etale m.left] [Surjective m.left] [IsMonHom p]
    (hp : A.multiplication n ≫ p = m) :
    IsFinite p.left ∧ Etale p.left ∧ Surjective p.left := by
  have hscalar : A.multiplication n ≫ p = p ^ n := by
    change ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n) ≫ p = p ^ n
    rw [MonObj.pow_comp, Category.id_comp]
  have he : p ≫ B.multiplication n = m :=
    (B.comp_multiplication n p).trans (hscalar.symm.trans hp)
  let : Etale (B.multiplication n).left :=
    (rational_multiplication_geometry qS B n hn).2.2.2.2
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

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.GroupDivisionLocus

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.ParameterPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.GroupDivisionLocus

/-! # Divisor Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.DivisorParameter

noncomputable section

/-! The actual closed division-by-a-unit locus carries its universal
finite etale isogeny. Its classification retains every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
section

theorem unit_divisor_unique
    {S : Scheme} {g h : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S) (n : ℕ)
    (hnUnit : IsUnit (n : Γ(S, ⊤)))
    {m p q : A.scheme ⟶ B.scheme}
    (hp : A.multiplication n ≫ p = m) (hq : A.multiplication n ≫ q = m) : p = q := by
  have hg := GroupDivisionLocus.unit_multiplication_geometry A n hnUnit
  let : IsFinite (A.multiplication n).left := hg.1
  let : Flat (A.multiplication n).left := hg.2.1
  let : Surjective (A.multiplication n).left := hg.2.2.1
  let : EffectiveEpi (A.multiplication n).left := inferInstance
  let : Epi (A.multiplication n) := Over.epi_of_epi_left _
  exact (cancel_epi (A.multiplication n)).mp (hp.trans hq.symm)

end

namespace UnitDivisionLocus

variable {S : Scheme} [IsLocallyNoetherian S] {g h : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
variable (m : Abelian.Schemes.AbelianScheme.Isogeny A B) (n : ℕ) (hnUnit : IsUnit (n : Γ(S, ⊤)))

include hnUnit in
private theorem exists_parameter :
    ∃ (Z : Over S) (j : Z ⟶ Over.mk (𝟙 S)), IsClosedImmersion j.left ∧
      ∀ T : Over S,
        (∃! p : {f : (A.pullback T.hom).scheme ⟶ (B.pullback T.hom).scheme // IsMonHom f},
          (A.pullback T.hom).multiplication n ≫ p.val = (Over.pullback T.hom).map m.hom) ↔
        ∃! y : T ⟶ Z, y ≫ j = Over.mkIdTerminal.from T :=
  GroupDivisionLocus.unit_group_division_closed_locus A B n hnUnit m.hom

def parameter : Over S := (exists_parameter A B m n hnUnit).choose

def inclusion : parameter A B m n hnUnit ⟶ Over.mk (𝟙 S) :=
  (exists_parameter A B m n hnUnit).choose_spec.choose

private theorem inclusion_spec :
    IsClosedImmersion (inclusion A B m n hnUnit).left ∧
      ∀ T : Over S,
        (∃! p : {f : (A.pullback T.hom).scheme ⟶ (B.pullback T.hom).scheme // IsMonHom f},
          (A.pullback T.hom).multiplication n ≫ p.val = (Over.pullback T.hom).map m.hom) ↔
        ∃! y : T ⟶ parameter A B m n hnUnit,
          y ≫ inclusion A B m n hnUnit = Over.mkIdTerminal.from T :=
  (exists_parameter A B m n hnUnit).choose_spec.choose_spec

instance parameter_isClosedImmersion : IsClosedImmersion (parameter A B m n hnUnit).hom := by
  have he : (inclusion A B m n hnUnit).left = (parameter A B m n hnUnit).hom := by
    have hw : (inclusion A B m n hnUnit).left ≫ 𝟙 S = (parameter A B m n hnUnit).hom :=
      (inclusion A B m n hnUnit).w
    exact (Category.comp_id _).symm.trans hw
  exact he ▸ (inclusion_spec A B m n hnUnit).1

instance parameter_locallyNoetherian : IsLocallyNoetherian (parameter A B m n hnUnit).left :=
  LocallyOfFiniteType.isLocallyNoetherian (parameter A B m n hnUnit).hom

instance parameter_affine [IsAffine S] : IsAffine (parameter A B m n hnUnit).left :=
  isAffine_of_isAffineHom (parameter A B m n hnUnit).hom

theorem parameter_hasPoint_iff (T : Over S) :
    Nonempty (T ⟶ parameter A B m n hnUnit) ↔
      ∃! p : {f : (A.pullback T.hom).scheme ⟶ (B.pullback T.hom).scheme // IsMonHom f},
        (A.pullback T.hom).multiplication n ≫ p.val = (Over.pullback T.hom).map m.hom := by
  constructor
  · rintro ⟨y⟩
    apply ((inclusion_spec A B m n hnUnit).2 T).mpr
    refine ⟨y, Over.mkIdTerminal.hom_ext _ _, ?_⟩
    intro z _
    apply Over.OverMorphism.ext
    apply (cancel_mono (parameter A B m n hnUnit).hom).mp
    exact z.w.trans y.w.symm
  · intro hp
    obtain ⟨y, _, _⟩ := ((inclusion_spec A B m n hnUnit).2 T).mp hp
    exact ⟨y⟩

theorem parameter_hasPoint_of_divisor {T : Over S}
    (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (B.pullback T.hom))
    (hp : (A.pullback T.hom).multiplication n ≫ p.hom = (Over.pullback T.hom).map m.hom) :
    Nonempty (T ⟶ parameter A B m n hnUnit) := by
  apply (parameter_hasPoint_iff A B m n hnUnit T).mpr
  refine ⟨⟨p.hom, inferInstance⟩, hp, ?_⟩
  intro z hz
  exact Subtype.ext (unit_divisor_unique
    (A.pullback T.hom) (B.pullback T.hom) n
    (Abelian.Schemes.level_unit_under_base_change T.hom n hnUnit) hz hp)

private theorem universal_division :
    ∃! p : {f : (A.pullback (parameter A B m n hnUnit).hom).scheme ⟶
        (B.pullback (parameter A B m n hnUnit).hom).scheme // IsMonHom f},
      (A.pullback (parameter A B m n hnUnit).hom).multiplication n ≫ p.val =
        (Over.pullback (parameter A B m n hnUnit).hom).map m.hom :=
  (parameter_hasPoint_iff A B m n hnUnit (parameter A B m n hnUnit)).mp ⟨𝟙 _⟩

def hom : (A.pullback (parameter A B m n hnUnit).hom).scheme ⟶
    (B.pullback (parameter A B m n hnUnit).hom).scheme :=
  (universal_division A B m n hnUnit).choose.val

instance hom_isMonHom : IsMonHom (UnitDivisionLocus.hom A B m n hnUnit) :=
  (universal_division A B m n hnUnit).choose.property

theorem hom_division :
    (A.pullback (parameter A B m n hnUnit).hom).multiplication n ≫ UnitDivisionLocus.hom A B m n hnUnit =
      (Over.pullback (parameter A B m n hnUnit).hom).map m.hom :=
  (universal_division A B m n hnUnit).choose_spec.1

variable [Etale m.hom.left]

private theorem hom_geometry : IsFinite (UnitDivisionLocus.hom A B m n hnUnit).left ∧
    Etale (UnitDivisionLocus.hom A B m n hnUnit).left ∧ Surjective (UnitDivisionLocus.hom A B m n hnUnit).left := by
  let b := (parameter A B m n hnUnit).hom
  let mb : (A.pullback b).scheme ⟶ (B.pullback b).scheme := (m.pullback b).hom
  let : IsFinite mb.left := (m.pullback b).finite
  let : Etale mb.left :=
    MorphismProperty.overPullbackMap b m.hom (inferInstance : Etale m.hom.left)
  let : Surjective mb.left := (m.pullback b).surjective
  exact GroupDivisionLocus.unit_divisor_finite_etale (A.pullback b) (B.pullback b) n
    (Abelian.Schemes.level_unit_under_base_change b n hnUnit)
    mb (UnitDivisionLocus.hom A B m n hnUnit) (hom_division A B m n hnUnit)

def isogeny : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (parameter A B m n hnUnit).hom)
    (B.pullback (parameter A B m n hnUnit).hom) := by
  let : Etale (UnitDivisionLocus.hom A B m n hnUnit).left := (hom_geometry A B m n hnUnit).2.1
  exact { hom := UnitDivisionLocus.hom A B m n hnUnit
          preservesGroup := inferInstance
          finite := (hom_geometry A B m n hnUnit).1
          flat := inferInstance
          surjective := (hom_geometry A B m n hnUnit).2.2 }

instance isogeny_etale : Etale (isogeny A B m n hnUnit).hom.left :=
  (hom_geometry A B m n hnUnit).2.1

def isogenyAt {T : Over S} (c : T ⟶ parameter A B m n hnUnit) :
    Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (B.pullback T.hom) :=
  Isogeny.ParameterPullback.isogenyParameterPullback A B (isogeny A B m n hnUnit) c

theorem isogenyAt_division {T : Over S} (c : T ⟶ parameter A B m n hnUnit) :
    (A.pullback T.hom).multiplication n ≫ (isogenyAt A B m n hnUnit c).hom =
      (Over.pullback T.hom).map m.hom :=
  Isogeny.ParameterPullback.isogenyParameterPullback_division A B (isogeny A B m n hnUnit) c n m.hom
    (hom_division A B m n hnUnit)

theorem isogenyAt_eq {T : Over S} (c : T ⟶ parameter A B m n hnUnit)
    (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (B.pullback T.hom))
    (hp : (A.pullback T.hom).multiplication n ≫ p.hom = (Over.pullback T.hom).map m.hom) :
    isogenyAt A B m n hnUnit c = p :=
  Isogeny.ParameterPullback.isogeny_eq_of_hom_eq (unit_divisor_unique
    (A.pullback T.hom) (B.pullback T.hom) n
    (Abelian.Schemes.level_unit_under_base_change T.hom n hnUnit) (isogenyAt_division A B m n hnUnit c) hp)

end UnitDivisionLocus

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.DivisorParameter

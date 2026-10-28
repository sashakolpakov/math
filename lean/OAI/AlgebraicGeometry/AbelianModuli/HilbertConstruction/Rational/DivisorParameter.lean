import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.ParameterPullback

/-! # Divisor Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.DivisorParameter.RationalDivisionLocus

noncomputable section

/-! The actual closed rational-division locus carries its universal
finite etale isogeny. Its classification retains every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} [IsLocallyNoetherian S] {g h : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
variable (m : Abelian.Schemes.AbelianScheme.Isogeny A B) (qS : S ⟶ Spec (.of ℚ)) (n : ℕ) (hn : 0 < n)

include qS hn in
private theorem exists_parameter :
    ∃ (Z : Over S) (j : Z ⟶ Over.mk (𝟙 S)), IsClosedImmersion j.left ∧
      ∀ T : Over S,
        (∃! p : {f : (A.pullback T.hom).scheme ⟶ (B.pullback T.hom).scheme // IsMonHom f},
          (A.pullback T.hom).multiplication n ≫ p.val = (Over.pullback T.hom).map m.hom) ↔
        ∃! y : T ⟶ Z, y ≫ j = Over.mkIdTerminal.from T :=
  GroupDivisionLocus.rational_group_division_closed_locus qS A B n hn m.hom

def parameter : Over S := (exists_parameter A B m qS n hn).choose

def inclusion : parameter A B m qS n hn ⟶ Over.mk (𝟙 S) :=
  (exists_parameter A B m qS n hn).choose_spec.choose

private theorem inclusion_spec :
    IsClosedImmersion (inclusion A B m qS n hn).left ∧
      ∀ T : Over S,
        (∃! p : {f : (A.pullback T.hom).scheme ⟶ (B.pullback T.hom).scheme // IsMonHom f},
          (A.pullback T.hom).multiplication n ≫ p.val = (Over.pullback T.hom).map m.hom) ↔
        ∃! y : T ⟶ parameter A B m qS n hn,
          y ≫ inclusion A B m qS n hn = Over.mkIdTerminal.from T :=
  (exists_parameter A B m qS n hn).choose_spec.choose_spec

instance parameter_isClosedImmersion : IsClosedImmersion (parameter A B m qS n hn).hom := by
  have he : (inclusion A B m qS n hn).left = (parameter A B m qS n hn).hom := by
    have hw : (inclusion A B m qS n hn).left ≫ 𝟙 S = (parameter A B m qS n hn).hom :=
      (inclusion A B m qS n hn).w
    exact (Category.comp_id _).symm.trans hw
  exact he ▸ (inclusion_spec A B m qS n hn).1

instance parameter_locallyNoetherian : IsLocallyNoetherian (parameter A B m qS n hn).left :=
  LocallyOfFiniteType.isLocallyNoetherian (parameter A B m qS n hn).hom

instance parameter_affine [IsAffine S] : IsAffine (parameter A B m qS n hn).left :=
  isAffine_of_isAffineHom (parameter A B m qS n hn).hom

theorem parameter_hasPoint_iff (T : Over S) :
    Nonempty (T ⟶ parameter A B m qS n hn) ↔
      ∃! p : {f : (A.pullback T.hom).scheme ⟶ (B.pullback T.hom).scheme // IsMonHom f},
        (A.pullback T.hom).multiplication n ≫ p.val = (Over.pullback T.hom).map m.hom := by
  constructor
  · rintro ⟨y⟩
    apply ((inclusion_spec A B m qS n hn).2 T).mpr
    refine ⟨y, Over.mkIdTerminal.hom_ext _ _, ?_⟩
    intro z _
    apply Over.OverMorphism.ext
    apply (cancel_mono (parameter A B m qS n hn).hom).mp
    exact z.w.trans y.w.symm
  · intro hp
    obtain ⟨y, _, _⟩ := ((inclusion_spec A B m qS n hn).2 T).mp hp
    exact ⟨y⟩

theorem parameter_hasPoint_of_divisor {T : Over S}
    (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (B.pullback T.hom))
    (hp : (A.pullback T.hom).multiplication n ≫ p.hom = (Over.pullback T.hom).map m.hom) :
    Nonempty (T ⟶ parameter A B m qS n hn) := by
  apply (parameter_hasPoint_iff A B m qS n hn T).mpr
  refine ⟨⟨p.hom, inferInstance⟩, hp, ?_⟩
  intro z hz
  exact Subtype.ext (Isogeny.ParameterPullback.rational_divisor_unique (T.hom ≫ qS)
    (A.pullback T.hom) (B.pullback T.hom) n hn hz hp)

private theorem universal_division :
    ∃! p : {f : (A.pullback (parameter A B m qS n hn).hom).scheme ⟶
        (B.pullback (parameter A B m qS n hn).hom).scheme // IsMonHom f},
      (A.pullback (parameter A B m qS n hn).hom).multiplication n ≫ p.val =
        (Over.pullback (parameter A B m qS n hn).hom).map m.hom :=
  (parameter_hasPoint_iff A B m qS n hn (parameter A B m qS n hn)).mp ⟨𝟙 _⟩

def hom : (A.pullback (parameter A B m qS n hn).hom).scheme ⟶
    (B.pullback (parameter A B m qS n hn).hom).scheme :=
  (universal_division A B m qS n hn).choose.val

instance hom_isMonHom : IsMonHom (RationalDivisionLocus.hom A B m qS n hn) :=
  (universal_division A B m qS n hn).choose.property

theorem hom_division :
    (A.pullback (parameter A B m qS n hn).hom).multiplication n ≫ RationalDivisionLocus.hom A B m qS n hn =
      (Over.pullback (parameter A B m qS n hn).hom).map m.hom :=
  (universal_division A B m qS n hn).choose_spec.1

variable [Etale m.hom.left]

private theorem hom_geometry : IsFinite (RationalDivisionLocus.hom A B m qS n hn).left ∧
    Etale (RationalDivisionLocus.hom A B m qS n hn).left ∧ Surjective (RationalDivisionLocus.hom A B m qS n hn).left := by
  let b := (parameter A B m qS n hn).hom
  let mb : (A.pullback b).scheme ⟶ (B.pullback b).scheme := (m.pullback b).hom
  let : IsFinite mb.left := (m.pullback b).finite
  let : Etale mb.left :=
    MorphismProperty.overPullbackMap b m.hom (inferInstance : Etale m.hom.left)
  let : Surjective mb.left := (m.pullback b).surjective
  exact GroupDivisionLocus.rational_divisor_finite_etale (b ≫ qS) (A.pullback b) (B.pullback b) n hn
    mb (RationalDivisionLocus.hom A B m qS n hn) (hom_division A B m qS n hn)

def isogeny : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (parameter A B m qS n hn).hom)
    (B.pullback (parameter A B m qS n hn).hom) := by
  let : Etale (RationalDivisionLocus.hom A B m qS n hn).left := (hom_geometry A B m qS n hn).2.1
  exact { hom := RationalDivisionLocus.hom A B m qS n hn
          preservesGroup := inferInstance
          finite := (hom_geometry A B m qS n hn).1
          flat := inferInstance
          surjective := (hom_geometry A B m qS n hn).2.2 }

instance isogeny_etale : Etale (isogeny A B m qS n hn).hom.left :=
  (hom_geometry A B m qS n hn).2.1

def isogenyAt {T : Over S} (c : T ⟶ parameter A B m qS n hn) :
    Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (B.pullback T.hom) :=
  Isogeny.ParameterPullback.isogenyParameterPullback A B (isogeny A B m qS n hn) c

theorem isogenyAt_division {T : Over S} (c : T ⟶ parameter A B m qS n hn) :
    (A.pullback T.hom).multiplication n ≫ (isogenyAt A B m qS n hn c).hom =
      (Over.pullback T.hom).map m.hom :=
  Isogeny.ParameterPullback.isogenyParameterPullback_division A B (isogeny A B m qS n hn) c n m.hom
    (hom_division A B m qS n hn)

theorem isogenyAt_eq {T : Over S} (c : T ⟶ parameter A B m qS n hn)
    (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (B.pullback T.hom))
    (hp : (A.pullback T.hom).multiplication n ≫ p.hom = (Over.pullback T.hom).map m.hom) :
    isogenyAt A B m qS n hn c = p :=
  Isogeny.ParameterPullback.isogeny_eq_of_hom_eq (Isogeny.ParameterPullback.rational_divisor_unique (T.hom ≫ qS)
    (A.pullback T.hom) (B.pullback T.hom) n hn (isogenyAt_division A B m qS n hn c) hp)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.DivisorParameter.RationalDivisionLocus

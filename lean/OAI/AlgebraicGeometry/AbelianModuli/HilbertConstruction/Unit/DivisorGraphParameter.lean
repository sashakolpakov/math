import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.DivisorParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GraphPowerParameterRestriction

/-! # Divisor Graph Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.DivisorGraphParameter.UnitDivisorGraphLocus

noncomputable section

/-! The closed division locus followed by the actual rigidified-frame
scheme represents the original divisor and normalized graph-power
comparison on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} [IsAffine S] [IsLocallyNoetherian S] {g : ℕ}
variable {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A)
variable (m : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) [Etale m.hom.left]
variable (d : ℕ) (hunit : IsUnit ((2 * d : ℕ) : Γ(S, ⊤)))
variable (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L : Line.Bundles.LineBundle A.scheme.left)

abbrev divisorBase : Over S :=
  DivisorParameter.UnitDivisionLocus.parameter A D.abelian m (2 * d) hunit

abbrev divisorIsogeny :
    Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (divisorBase D m d hunit).hom)
      (D.pullback (divisorBase D m d hunit).hom).abelian :=
  DivisorParameter.UnitDivisionLocus.isogeny A D.abelian m (2 * d) hunit

abbrev frameBase : Over (divisorBase D m d hunit).left :=
  Affine.GraphPowerCompatibilityParameter.AffineRawGraphPower.parameter (A.pullback (divisorBase D m d hunit).hom)
    (D.pullback (divisorBase D m d hunit).hom) (divisorIsogeny D m d hunit).hom
    (P.baseChange (divisorBase D m d hunit).hom)
    (L.pullback (pullback.fst A.scheme.hom (divisorBase D m d hunit).hom)) d

local instance divisorBase_closed : IsClosedImmersion (divisorBase D m d hunit).hom :=
  DivisorParameter.UnitDivisionLocus.parameter_isClosedImmersion A D.abelian m (2 * d) hunit

local instance frameBase_locallyOfFiniteType :
    LocallyOfFiniteType (frameBase D m d hunit P L).hom :=
  Affine.GraphPowerCompatibilityParameter.AffineRawGraphPower.parameter_locallyOfFiniteType
    (A.pullback (divisorBase D m d hunit).hom)
    (D.pullback (divisorBase D m d hunit).hom) (divisorIsogeny D m d hunit).hom
    (P.baseChange (divisorBase D m d hunit).hom)
    (L.pullback (pullback.fst A.scheme.hom (divisorBase D m d hunit).hom)) d

local instance frameBase_quasiCompact : QuasiCompact (frameBase D m d hunit P L).hom :=
  Affine.GraphPowerCompatibilityParameter.AffineRawGraphPower.parameter_quasiCompact
    (A.pullback (divisorBase D m d hunit).hom)
    (D.pullback (divisorBase D m d hunit).hom) (divisorIsogeny D m d hunit).hom
    (P.baseChange (divisorBase D m d hunit).hom)
    (L.pullback (pullback.fst A.scheme.hom (divisorBase D m d hunit).hom)) d

local instance frameBase_mono : Mono (frameBase D m d hunit P L).hom :=
  Affine.GraphPowerCompatibilityParameter.AffineRawGraphPower.parameter_mono
    (A.pullback (divisorBase D m d hunit).hom)
    (D.pullback (divisorBase D m d hunit).hom) (divisorIsogeny D m d hunit).hom
    (P.baseChange (divisorBase D m d hunit).hom)
    (L.pullback (pullback.fst A.scheme.hom (divisorBase D m d hunit).hom)) d

def parameter : Over S :=
  (Over.map (divisorBase D m d hunit).hom).obj (frameBase D m d hunit P L)

def toDivisor : parameter D m d hunit P L ⟶ divisorBase D m d hunit :=
  Over.homMk (frameBase D m d hunit P L).hom rfl

instance parameter_locallyOfFiniteType : LocallyOfFiniteType (parameter D m d hunit P L).hom := by
  change LocallyOfFiniteType ((frameBase D m d hunit P L).hom ≫ (divisorBase D m d hunit).hom)
  infer_instance

instance parameter_quasiCompact : QuasiCompact (parameter D m d hunit P L).hom := by
  change QuasiCompact ((frameBase D m d hunit P L).hom ≫ (divisorBase D m d hunit).hom)
  infer_instance

instance parameter_mono : Mono (parameter D m d hunit P L).hom := by
  change Mono ((frameBase D m d hunit P L).hom ≫ (divisorBase D m d hunit).hom)
  infer_instance

instance parameter_locallyNoetherian : IsLocallyNoetherian (parameter D m d hunit P L).left :=
  LocallyOfFiniteType.isLocallyNoetherian (parameter D m d hunit P L).hom

def isogeny : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (parameter D m d hunit P L).hom)
    (D.abelian.pullback (parameter D m d hunit P L).hom) :=
  DivisorParameter.UnitDivisionLocus.isogenyAt A D.abelian m (2 * d) hunit
    (toDivisor D m d hunit P L)

theorem isogeny_division :
    (A.pullback (parameter D m d hunit P L).hom).multiplication (2 * d) ≫
      (isogeny D m d hunit P L).hom =
        (Over.pullback (parameter D m d hunit P L).hom).map m.hom :=
  DivisorParameter.UnitDivisionLocus.isogenyAt_division A D.abelian m (2 * d) hunit
    (toDivisor D m d hunit P L)

instance isogeny_etale : Etale (isogeny D m d hunit P L).hom.left :=
  Isogeny.ParameterPullback.isogenyParameterPullback_etale A D.abelian (divisorIsogeny D m d hunit)
    (toDivisor D m d hunit P L)

def isogenyAt {T : Over S} (c : T ⟶ parameter D m d hunit P L) :
    Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (D.abelian.pullback T.hom) :=
  Isogeny.ParameterPullback.isogenyParameterPullback A D.abelian (isogeny D m d hunit P L) c

theorem isogenyAt_division {T : Over S} (c : T ⟶ parameter D m d hunit P L) :
    (A.pullback T.hom).multiplication (2 * d) ≫ (isogenyAt D m d hunit P L c).hom =
      (Over.pullback T.hom).map m.hom :=
  Isogeny.ParameterPullback.isogenyParameterPullback_division A D.abelian (isogeny D m d hunit P L) c (2 * d) m.hom
    (isogeny_division D m d hunit P L)

theorem isogenyAt_eq {T : Over S} (c : T ⟶ parameter D m d hunit P L)
    (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (D.abelian.pullback T.hom))
    (hp : (A.pullback T.hom).multiplication (2 * d) ≫ p.hom = (Over.pullback T.hom).map m.hom) :
    isogenyAt D m d hunit P L c = p :=
  Isogeny.ParameterPullback.isogeny_eq_of_hom_eq (DivisorParameter.unit_divisor_unique
    (A.pullback T.hom) (D.abelian.pullback T.hom) (2 * d)
    (Abelian.Schemes.level_unit_under_base_change T.hom (2 * d) hunit)
    (isogenyAt_division D m d hunit P L c) hp)

theorem parameter_hasPoint_iff_of_division {T : Over S}
    (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (D.abelian.pullback T.hom))
    (hp : (A.pullback T.hom).multiplication (2 * d) ≫ p.hom = (Over.pullback T.hom).map m.hom) :
    Nonempty (T ⟶ parameter D m d hunit P L) ↔
      Nonempty (((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom T.hom)).sheaf ≅
        ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback T.hom) p.hom).tensorPower d).sheaf) := by
  let Z := divisorBase D m d hunit
  let Q := divisorIsogeny D m d hunit
  have he (z : T ⟶ Z) : Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange z Q.hom = p.hom := by
    have h := congrArg Abelian.Schemes.AbelianScheme.Isogeny.hom
      (DivisorParameter.UnitDivisionLocus.isogenyAt_eq A D.abelian m (2 * d) hunit z p hp)
    exact (Isogeny.ParameterPullback.isogenyParameterPullback_hom A D.abelian Q z).symm.trans h
  constructor
  · rintro ⟨c⟩
    let z : T ⟶ Z := c ≫ toDivisor D m d hunit P L
    let x : Over.mk z.left ⟶ frameBase D m d hunit P L := Over.homMk c.left rfl
    have h := (Affine.GraphPowerParameterRestriction.AffineRawGraphPower.parameter_hasPoint_iff_restriction A D z Q.hom P L d).mp ⟨x⟩
    rw [he z] at h
    exact h
  · intro hpG
    obtain ⟨z⟩ := DivisorParameter.UnitDivisionLocus.parameter_hasPoint_of_divisor A D.abelian m (2 * d) hunit p hp
    obtain ⟨x⟩ := (Affine.GraphPowerParameterRestriction.AffineRawGraphPower.parameter_hasPoint_iff_restriction A D z Q.hom P L d).mpr
      (by rw [he z]; exact hpG)
    refine ⟨Over.homMk x.left ?_⟩
    change x.left ≫ ((frameBase D m d hunit P L).hom ≫ Z.hom) = T.hom
    have hx : x.left ≫ (frameBase D m d hunit P L).hom = z.left := x.w
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k : T.left ⟶ Z.left => k ≫ Z.hom) hx).trans z.w)

theorem parameter_hasPoint_iff (T : Over S) :
    Nonempty (T ⟶ parameter D m d hunit P L) ↔
      ∃ p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (D.abelian.pullback T.hom),
        ((A.pullback T.hom).multiplication (2 * d) ≫ p.hom = (Over.pullback T.hom).map m.hom) ∧
        Nonempty (((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom T.hom)).sheaf ≅
          ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback T.hom) p.hom).tensorPower d).sheaf) := by
  constructor
  · rintro ⟨c⟩
    refine ⟨isogenyAt D m d hunit P L c, isogenyAt_division D m d hunit P L c, ?_⟩
    exact (parameter_hasPoint_iff_of_division D m d hunit P L
      (isogenyAt D m d hunit P L c) (isogenyAt_division D m d hunit P L c)).mp ⟨c⟩
  · rintro ⟨p, hp, hG⟩
    exact (parameter_hasPoint_iff_of_division D m d hunit P L p hp).mpr hG

def universalIso :
    ((A.zeroNormalizedBundle L).pullback
      (pullback.fst A.scheme.hom (parameter D m d hunit P L).hom)).sheaf ≅
    ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback (parameter D m d hunit P L).hom)
      (isogeny D m d hunit P L).hom).tensorPower d).sheaf :=
  Classical.choice ((parameter_hasPoint_iff_of_division D m d hunit P L
    (isogeny D m d hunit P L) (isogeny_division D m d hunit P L)).mp ⟨𝟙 _⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.DivisorGraphParameter.UnitDivisorGraphLocus

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.DivisorParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GraphPowerParameterRestriction

/-! # Divisor Graph Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.DivisorGraphParameter.RationalDivisorGraphLocus

noncomputable section

/-! The closed division locus followed by the actual rigidified-frame
scheme represents the original divisor and normalized graph-power
comparison on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} [IsAffine S] [IsLocallyNoetherian S] {g : ℕ}
variable {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A)
variable (m : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) [Etale m.hom.left]
variable (qS : S ⟶ Spec (.of ℚ)) (d : ℕ) (hd : 0 < d)
variable (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L : Line.Bundles.LineBundle A.scheme.left)

abbrev divisorBase : Over S :=
  DivisorParameter.RationalDivisionLocus.parameter A D.abelian m qS (2 * d) (Nat.mul_pos (by decide) hd)

abbrev divisorIsogeny :
    Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (divisorBase D m qS d hd).hom)
      (D.pullback (divisorBase D m qS d hd).hom).abelian :=
  DivisorParameter.RationalDivisionLocus.isogeny A D.abelian m qS (2 * d) (Nat.mul_pos (by decide) hd)

abbrev frameBase : Over (divisorBase D m qS d hd).left :=
  Affine.GraphPowerCompatibilityParameter.AffineRawGraphPower.parameter (A.pullback (divisorBase D m qS d hd).hom)
    (D.pullback (divisorBase D m qS d hd).hom) (divisorIsogeny D m qS d hd).hom
    (P.baseChange (divisorBase D m qS d hd).hom)
    (L.pullback (pullback.fst A.scheme.hom (divisorBase D m qS d hd).hom)) d

local instance divisorBase_closed : IsClosedImmersion (divisorBase D m qS d hd).hom :=
  DivisorParameter.RationalDivisionLocus.parameter_isClosedImmersion A D.abelian m qS
    (2 * d) (Nat.mul_pos (by decide) hd)

local instance frameBase_locallyOfFiniteType :
    LocallyOfFiniteType (frameBase D m qS d hd P L).hom :=
  Affine.GraphPowerCompatibilityParameter.AffineRawGraphPower.parameter_locallyOfFiniteType
    (A.pullback (divisorBase D m qS d hd).hom)
    (D.pullback (divisorBase D m qS d hd).hom) (divisorIsogeny D m qS d hd).hom
    (P.baseChange (divisorBase D m qS d hd).hom)
    (L.pullback (pullback.fst A.scheme.hom (divisorBase D m qS d hd).hom)) d

local instance frameBase_quasiCompact : QuasiCompact (frameBase D m qS d hd P L).hom :=
  Affine.GraphPowerCompatibilityParameter.AffineRawGraphPower.parameter_quasiCompact
    (A.pullback (divisorBase D m qS d hd).hom)
    (D.pullback (divisorBase D m qS d hd).hom) (divisorIsogeny D m qS d hd).hom
    (P.baseChange (divisorBase D m qS d hd).hom)
    (L.pullback (pullback.fst A.scheme.hom (divisorBase D m qS d hd).hom)) d

local instance frameBase_mono : Mono (frameBase D m qS d hd P L).hom :=
  Affine.GraphPowerCompatibilityParameter.AffineRawGraphPower.parameter_mono
    (A.pullback (divisorBase D m qS d hd).hom)
    (D.pullback (divisorBase D m qS d hd).hom) (divisorIsogeny D m qS d hd).hom
    (P.baseChange (divisorBase D m qS d hd).hom)
    (L.pullback (pullback.fst A.scheme.hom (divisorBase D m qS d hd).hom)) d

def parameter : Over S :=
  (Over.map (divisorBase D m qS d hd).hom).obj (frameBase D m qS d hd P L)

def toDivisor : parameter D m qS d hd P L ⟶ divisorBase D m qS d hd :=
  Over.homMk (frameBase D m qS d hd P L).hom rfl

instance parameter_locallyOfFiniteType : LocallyOfFiniteType (parameter D m qS d hd P L).hom := by
  change LocallyOfFiniteType ((frameBase D m qS d hd P L).hom ≫ (divisorBase D m qS d hd).hom)
  infer_instance

instance parameter_quasiCompact : QuasiCompact (parameter D m qS d hd P L).hom := by
  change QuasiCompact ((frameBase D m qS d hd P L).hom ≫ (divisorBase D m qS d hd).hom)
  infer_instance

instance parameter_mono : Mono (parameter D m qS d hd P L).hom := by
  change Mono ((frameBase D m qS d hd P L).hom ≫ (divisorBase D m qS d hd).hom)
  infer_instance

instance parameter_locallyNoetherian : IsLocallyNoetherian (parameter D m qS d hd P L).left :=
  LocallyOfFiniteType.isLocallyNoetherian (parameter D m qS d hd P L).hom

def isogeny : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (parameter D m qS d hd P L).hom)
    (D.abelian.pullback (parameter D m qS d hd P L).hom) :=
  DivisorParameter.RationalDivisionLocus.isogenyAt A D.abelian m qS (2 * d) (Nat.mul_pos (by decide) hd)
    (toDivisor D m qS d hd P L)

theorem isogeny_division :
    (A.pullback (parameter D m qS d hd P L).hom).multiplication (2 * d) ≫
      (isogeny D m qS d hd P L).hom =
        (Over.pullback (parameter D m qS d hd P L).hom).map m.hom :=
  DivisorParameter.RationalDivisionLocus.isogenyAt_division A D.abelian m qS (2 * d) (Nat.mul_pos (by decide) hd)
    (toDivisor D m qS d hd P L)

instance isogeny_etale : Etale (isogeny D m qS d hd P L).hom.left :=
  Isogeny.ParameterPullback.isogenyParameterPullback_etale A D.abelian (divisorIsogeny D m qS d hd)
    (toDivisor D m qS d hd P L)

def isogenyAt {T : Over S} (c : T ⟶ parameter D m qS d hd P L) :
    Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (D.abelian.pullback T.hom) :=
  Isogeny.ParameterPullback.isogenyParameterPullback A D.abelian (isogeny D m qS d hd P L) c

theorem isogenyAt_division {T : Over S} (c : T ⟶ parameter D m qS d hd P L) :
    (A.pullback T.hom).multiplication (2 * d) ≫ (isogenyAt D m qS d hd P L c).hom =
      (Over.pullback T.hom).map m.hom :=
  Isogeny.ParameterPullback.isogenyParameterPullback_division A D.abelian (isogeny D m qS d hd P L) c (2 * d) m.hom
    (isogeny_division D m qS d hd P L)

theorem isogenyAt_eq {T : Over S} (c : T ⟶ parameter D m qS d hd P L)
    (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (D.abelian.pullback T.hom))
    (hp : (A.pullback T.hom).multiplication (2 * d) ≫ p.hom = (Over.pullback T.hom).map m.hom) :
    isogenyAt D m qS d hd P L c = p :=
  Isogeny.ParameterPullback.isogeny_eq_of_hom_eq (Isogeny.ParameterPullback.rational_divisor_unique (T.hom ≫ qS)
    (A.pullback T.hom) (D.abelian.pullback T.hom) (2 * d) (Nat.mul_pos (by decide) hd)
    (isogenyAt_division D m qS d hd P L c) hp)

theorem parameter_hasPoint_iff_of_division {T : Over S}
    (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (D.abelian.pullback T.hom))
    (hp : (A.pullback T.hom).multiplication (2 * d) ≫ p.hom = (Over.pullback T.hom).map m.hom) :
    Nonempty (T ⟶ parameter D m qS d hd P L) ↔
      Nonempty (((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom T.hom)).sheaf ≅
        ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback T.hom) p.hom).tensorPower d).sheaf) := by
  let Z := divisorBase D m qS d hd
  let Q := divisorIsogeny D m qS d hd
  have he (z : T ⟶ Z) : Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange z Q.hom = p.hom := by
    have h := congrArg Abelian.Schemes.AbelianScheme.Isogeny.hom
      (DivisorParameter.RationalDivisionLocus.isogenyAt_eq A D.abelian m qS (2 * d)
        (Nat.mul_pos (by decide) hd) z p hp)
    exact (Isogeny.ParameterPullback.isogenyParameterPullback_hom A D.abelian Q z).symm.trans h
  constructor
  · rintro ⟨c⟩
    let z : T ⟶ Z := c ≫ toDivisor D m qS d hd P L
    let x : Over.mk z.left ⟶ frameBase D m qS d hd P L := Over.homMk c.left rfl
    have h := (Affine.GraphPowerParameterRestriction.AffineRawGraphPower.parameter_hasPoint_iff_restriction A D z Q.hom P L d).mp ⟨x⟩
    rw [he z] at h
    exact h
  · intro hpG
    obtain ⟨z⟩ := DivisorParameter.RationalDivisionLocus.parameter_hasPoint_of_divisor A D.abelian m qS (2 * d)
      (Nat.mul_pos (by decide) hd) p hp
    obtain ⟨x⟩ := (Affine.GraphPowerParameterRestriction.AffineRawGraphPower.parameter_hasPoint_iff_restriction A D z Q.hom P L d).mpr
      (by rw [he z]; exact hpG)
    refine ⟨Over.homMk x.left ?_⟩
    change x.left ≫ ((frameBase D m qS d hd P L).hom ≫ Z.hom) = T.hom
    have hx : x.left ≫ (frameBase D m qS d hd P L).hom = z.left := x.w
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k : T.left ⟶ Z.left => k ≫ Z.hom) hx).trans z.w)

theorem parameter_hasPoint_iff (T : Over S) :
    Nonempty (T ⟶ parameter D m qS d hd P L) ↔
      ∃ p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (D.abelian.pullback T.hom),
        ((A.pullback T.hom).multiplication (2 * d) ≫ p.hom = (Over.pullback T.hom).map m.hom) ∧
        Nonempty (((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom T.hom)).sheaf ≅
          ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback T.hom) p.hom).tensorPower d).sheaf) := by
  constructor
  · rintro ⟨c⟩
    refine ⟨isogenyAt D m qS d hd P L c, isogenyAt_division D m qS d hd P L c, ?_⟩
    exact (parameter_hasPoint_iff_of_division D m qS d hd P L
      (isogenyAt D m qS d hd P L c) (isogenyAt_division D m qS d hd P L c)).mp ⟨c⟩
  · rintro ⟨p, hp, hG⟩
    exact (parameter_hasPoint_iff_of_division D m qS d hd P L p hp).mpr hG

def universalIso :
    ((A.zeroNormalizedBundle L).pullback
      (pullback.fst A.scheme.hom (parameter D m qS d hd P L).hom)).sheaf ≅
    ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback (parameter D m qS d hd P L).hom)
      (isogeny D m qS d hd P L).hom).tensorPower d).sheaf :=
  Classical.choice ((parameter_hasPoint_iff_of_division D m qS d hd P L
    (isogeny D m qS d hd P L) (isogeny_division D m qS d hd P L)).mp ⟨𝟙 _⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.DivisorGraphParameter.RationalDivisorGraphLocus

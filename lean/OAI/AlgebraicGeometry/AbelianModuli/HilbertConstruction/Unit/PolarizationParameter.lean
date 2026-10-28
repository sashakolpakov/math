import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.DivisorGraphParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.PolarizationTypeLocus
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.TranslationDivisorPolarization

/-! # Polarization Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.PolarizationParameter.UnitPolarizationLocus

noncomputable section

/-! The actual closed division locus, normalized graph-frame scheme,
and clopen original kernel-type locus give one quasi-compact locally
finite-type monomorphism. Its universal divisor is an original
polarization, and its classification holds on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} [IsAffine S] [IsLocallyNoetherian S] {g : ℕ}
variable {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A)
variable (m : Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) [Etale m.hom.left]
variable (d : ℕ) (hunit : IsUnit ((2 * d : ℕ) : Γ(S, ⊤)))
variable (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
variable (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i)

abbrev graphBase : Over S := DivisorGraphParameter.UnitDivisorGraphLocus.parameter D m d hunit P L

abbrev graphIsogeny :
    Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (graphBase D m d hunit P L).hom)
      (D.abelian.pullback (graphBase D m d hunit P L).hom) :=
  DivisorGraphParameter.UnitDivisorGraphLocus.isogeny D m d hunit P L

include hδ in
private theorem exists_typeOpen :
    ∃ U : (graphBase D m d hunit P L).left.Opens,
      IsClopen (U : Set (graphBase D m d hunit P L).left) ∧
      ∀ (T : Scheme) (b : T ⟶ (graphBase D m d hunit P L).left),
        (∃ c : T ⟶ U, c ≫ U.ι = b) ↔
          ((graphIsogeny D m d hunit P L).pullback b).HasPolarizationType δ :=
  Isogeny.PolarizationTypeLocus.isogeny_polarizationTypeOpen (graphIsogeny D m d hunit P L) δ hδ

def typeOpen : (graphBase D m d hunit P L).left.Opens :=
  (exists_typeOpen D m d hunit P L δ hδ).choose

private theorem typeOpen_spec :
    IsClopen (typeOpen D m d hunit P L δ hδ : Set (graphBase D m d hunit P L).left) ∧
      ∀ (T : Scheme) (b : T ⟶ (graphBase D m d hunit P L).left),
        (∃ c : T ⟶ typeOpen D m d hunit P L δ hδ,
          c ≫ (typeOpen D m d hunit P L δ hδ).ι = b) ↔
          ((graphIsogeny D m d hunit P L).pullback b).HasPolarizationType δ :=
  (exists_typeOpen D m d hunit P L δ hδ).choose_spec

instance typeOpen_inclusion_isClosedImmersion :
    IsClosedImmersion (typeOpen D m d hunit P L δ hδ).ι := by
  apply IsClosedImmersion.of_isPreimmersion
  simpa only [Scheme.Opens.range_ι] using (typeOpen_spec D m d hunit P L δ hδ).1.isClosed

def parameter : Over S :=
  Over.mk ((typeOpen D m d hunit P L δ hδ).ι ≫ (graphBase D m d hunit P L).hom)

def toGraph : parameter D m d hunit P L δ hδ ⟶ graphBase D m d hunit P L :=
  Over.homMk (typeOpen D m d hunit P L δ hδ).ι rfl

instance parameter_locallyOfFiniteType :
    LocallyOfFiniteType (parameter D m d hunit P L δ hδ).hom := by
  change LocallyOfFiniteType
    ((typeOpen D m d hunit P L δ hδ).ι ≫ (graphBase D m d hunit P L).hom)
  infer_instance

instance parameter_quasiCompact : QuasiCompact (parameter D m d hunit P L δ hδ).hom := by
  change QuasiCompact
    ((typeOpen D m d hunit P L δ hδ).ι ≫ (graphBase D m d hunit P L).hom)
  infer_instance

instance parameter_mono : Mono (parameter D m d hunit P L δ hδ).hom := by
  change Mono ((typeOpen D m d hunit P L δ hδ).ι ≫ (graphBase D m d hunit P L).hom)
  infer_instance

instance parameter_locallyNoetherian :
    IsLocallyNoetherian (parameter D m d hunit P L δ hδ).left :=
  LocallyOfFiniteType.isLocallyNoetherian (parameter D m d hunit P L δ hδ).hom

theorem parameter_hasPoint_iff (T : Over S) :
    Nonempty (T ⟶ parameter D m d hunit P L δ hδ) ↔
      ∃ p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (D.abelian.pullback T.hom),
        ((A.pullback T.hom).multiplication (2 * d) ≫ p.hom = (Over.pullback T.hom).map m.hom) ∧
        p.HasPolarizationType δ ∧
        Nonempty (((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom T.hom)).sheaf ≅
          ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback T.hom) p.hom).tensorPower d).sheaf) := by
  constructor
  · rintro ⟨a⟩
    let b := a ≫ toGraph D m d hunit P L δ hδ
    let p := DivisorGraphParameter.UnitDivisorGraphLocus.isogenyAt D m d hunit P L b
    have hp : (A.pullback T.hom).multiplication (2 * d) ≫ p.hom =
        (Over.pullback T.hom).map m.hom :=
      DivisorGraphParameter.UnitDivisorGraphLocus.isogenyAt_division D m d hunit P L b
    have ht : ((graphIsogeny D m d hunit P L).pullback b.left).HasPolarizationType δ :=
      ((typeOpen_spec D m d hunit P L δ hδ).2 T.left b.left).mp ⟨a.left, rfl⟩
    refine ⟨p, hp, ?_, ?_⟩
    · exact (Isogeny.ParameterPullback.isogenyParameterPullback_hasType_iff A D.abelian
        (graphIsogeny D m d hunit P L) b δ).mpr ht
    · exact (DivisorGraphParameter.UnitDivisorGraphLocus.parameter_hasPoint_iff_of_division
        D m d hunit P L p hp).mp ⟨b⟩
  · rintro ⟨p, hp, ht, hG⟩
    obtain ⟨b⟩ := (DivisorGraphParameter.UnitDivisorGraphLocus.parameter_hasPoint_iff_of_division
      D m d hunit P L p hp).mpr hG
    have he : DivisorGraphParameter.UnitDivisorGraphLocus.isogenyAt D m d hunit P L b = p :=
      DivisorGraphParameter.UnitDivisorGraphLocus.isogenyAt_eq D m d hunit P L b p hp
    have ht' : (DivisorGraphParameter.UnitDivisorGraphLocus.isogenyAt D m d hunit P L b).HasPolarizationType δ :=
      he.symm ▸ ht
    have ht'' : ((graphIsogeny D m d hunit P L).pullback b.left).HasPolarizationType δ :=
      (Isogeny.ParameterPullback.isogenyParameterPullback_hasType_iff A D.abelian
        (graphIsogeny D m d hunit P L) b δ).mp ht'
    obtain ⟨c, hc⟩ := ((typeOpen_spec D m d hunit P L δ hδ).2 T.left b.left).mpr ht''
    refine ⟨Over.homMk c ?_⟩
    change c ≫ ((typeOpen D m d hunit P L δ hδ).ι ≫ (graphBase D m d hunit P L).hom) = T.hom
    rw [← Category.assoc, hc, b.w]

private theorem universal_data :
    ∃ p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (parameter D m d hunit P L δ hδ).hom)
        (D.abelian.pullback (parameter D m d hunit P L δ hδ).hom),
      ((A.pullback (parameter D m d hunit P L δ hδ).hom).multiplication (2 * d) ≫ p.hom =
        (Over.pullback (parameter D m d hunit P L δ hδ).hom).map m.hom) ∧
      p.HasPolarizationType δ ∧
      Nonempty (((A.zeroNormalizedBundle L).pullback
        (pullback.fst A.scheme.hom (parameter D m d hunit P L δ hδ).hom)).sheaf ≅
        ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback (parameter D m d hunit P L δ hδ).hom)
          p.hom).tensorPower d).sheaf) :=
  (parameter_hasPoint_iff D m d hunit P L δ hδ (parameter D m d hunit P L δ hδ)).mp ⟨𝟙 _⟩

def isogeny :
    Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (parameter D m d hunit P L δ hδ).hom)
      (D.abelian.pullback (parameter D m d hunit P L δ hδ).hom) :=
  (universal_data D m d hunit P L δ hδ).choose

theorem isogeny_division :
    (A.pullback (parameter D m d hunit P L δ hδ).hom).multiplication (2 * d) ≫
      (isogeny D m d hunit P L δ hδ).hom =
        (Over.pullback (parameter D m d hunit P L δ hδ).hom).map m.hom :=
  (universal_data D m d hunit P L δ hδ).choose_spec.1

theorem isogeny_type : (isogeny D m d hunit P L δ hδ).HasPolarizationType δ :=
  (universal_data D m d hunit P L δ hδ).choose_spec.2.1

def universalIso :
    ((A.zeroNormalizedBundle L).pullback
      (pullback.fst A.scheme.hom (parameter D m d hunit P L δ hδ).hom)).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle (D.pullback (parameter D m d hunit P L δ hδ).hom)
        (isogeny D m d hunit P L δ hδ).hom).tensorPower d).sheaf :=
  (universal_data D m d hunit P L δ hδ).choose_spec.2.2.some

theorem universalIsogeny_parameterPullback_eq {T : Over S}
    (a : T ⟶ parameter D m d hunit P L δ hδ)
    (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (D.abelian.pullback T.hom))
    (hp : (A.pullback T.hom).multiplication (2 * d) ≫ p.hom = (Over.pullback T.hom).map m.hom) :
    Isogeny.ParameterPullback.isogenyParameterPullback A D.abelian (isogeny D m d hunit P L δ hδ) a = p :=
  Isogeny.ParameterPullback.isogeny_eq_of_hom_eq (DivisorParameter.unit_divisor_unique
    (A.pullback T.hom) (D.abelian.pullback T.hom) (2 * d)
    (Abelian.Schemes.level_unit_under_base_change T.hom (2 * d) hunit)
    (Isogeny.ParameterPullback.isogenyParameterPullback_division A D.abelian (isogeny D m d hunit P L δ hδ) a
      (2 * d) m.hom (isogeny_division D m d hunit P L δ hδ)) hp)

def polarization (hd : 0 < d) (hL : L.IsAmple)
    (recover : (D.poincare.pullback (m.hom ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf) :
    PolarizationData.Polarization (D.pullback (parameter D m d hunit P L δ hδ).hom) δ :=
  PolarizationData.Polarization.ofBaseChangedAmpleUnitTranslationDivisor D (parameter D m d hunit P L δ hδ).hom
    (isogeny D m d hunit P L δ hδ) δ (isogeny_type D m d hunit P L δ hδ)
    d hd hunit m.hom L hL recover (isogeny_division D m d hunit P L δ hδ)
    (universalIso D m d hunit P L δ hδ)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.PolarizationParameter.UnitPolarizationLocus

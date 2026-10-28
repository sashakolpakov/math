import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.ProjectiveDual
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PolarizationParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange

/-! # Projective Polarization Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.ProjectivePolarizationParameter.RationalProjectivePolarizationLocus

noncomputable section

/-! A projective abelian scheme with an ample line over a Noetherian
rational affine base has an actual rational polarization parameter.
The dual and its inducing isogeny come from the ample translation
quotient. The parameter classifies the original divisor, kernel type,
and graph-power conditions on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {R : Type} [CommRing R] [IsNoetherianRing R] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of R))) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (L : Line.Bundles.LineBundle A.scheme.left) (qS : Spec (.of R) ⟶ Spec (.of ℚ)) (hL : L.IsAmple)

/-- Choose the actual quotient by the full ample translation kernel. -/
def translationQuotient : Ample.TranslationQuotient.AmpleTranslationQuotient A L P :=
  Classical.choice (Ample.TranslationQuotient.ampleTranslationQuotient_nonempty A L P qS hL)

/-- Its Poincare bundle and dual represent the original Picard problem. -/
def dualData : Dual.Data.DualAbelianData A :=
  (translationQuotient A P L qS hL).dualData qS hL

def inducingIsogeny : Abelian.Schemes.AbelianScheme.Isogeny A (RationalProjectivePolarizationLocus.dualData A P L qS hL).abelian :=
  (translationQuotient A P L qS hL).dualIsogeny qS hL

instance inducingIsogeny_etale : Etale (inducingIsogeny A P L qS hL).hom.left :=
  (translationQuotient A P L qS hL).dualIsogeny_etale qS hL

def inducingPoincareRecovery :
    ((RationalProjectivePolarizationLocus.dualData A P L qS hL).poincare.pullback
      ((inducingIsogeny A P L qS hL).hom ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
        (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf :=
  (translationQuotient A P L qS hL).dualPoincareRecovery qS hL

variable (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i)

/-- The actual division, graph-frame, and original kernel-type locus. -/
def parameter : Over (Spec (.of R)) :=
  PolarizationParameter.RationalPolarizationLocus.parameter (RationalProjectivePolarizationLocus.dualData A P L qS hL) (inducingIsogeny A P L qS hL)
    qS d hd P L δ hδ

instance parameter_locallyOfFiniteType :
    LocallyOfFiniteType (parameter A P L qS hL d hd δ hδ).hom :=
  PolarizationParameter.RationalPolarizationLocus.parameter_locallyOfFiniteType
    (RationalProjectivePolarizationLocus.dualData A P L qS hL) (inducingIsogeny A P L qS hL) qS d hd P L δ hδ

instance parameter_quasiCompact : QuasiCompact (parameter A P L qS hL d hd δ hδ).hom :=
  PolarizationParameter.RationalPolarizationLocus.parameter_quasiCompact
    (RationalProjectivePolarizationLocus.dualData A P L qS hL) (inducingIsogeny A P L qS hL) qS d hd P L δ hδ

instance parameter_mono : Mono (parameter A P L qS hL d hd δ hδ).hom :=
  PolarizationParameter.RationalPolarizationLocus.parameter_mono
    (RationalProjectivePolarizationLocus.dualData A P L qS hL) (inducingIsogeny A P L qS hL) qS d hd P L δ hδ

instance parameter_locallyNoetherian :
    IsLocallyNoetherian (parameter A P L qS hL d hd δ hδ).left :=
  PolarizationParameter.RationalPolarizationLocus.parameter_locallyNoetherian
    (RationalProjectivePolarizationLocus.dualData A P L qS hL) (inducingIsogeny A P L qS hL) qS d hd P L δ hδ

/-- Classification on arbitrary schemes over the original affine base. -/
theorem parameter_hasPoint_iff (T : Over (Spec (.of R))) :
    Nonempty (T ⟶ parameter A P L qS hL d hd δ hδ) ↔
      ∃ p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom)
          ((RationalProjectivePolarizationLocus.dualData A P L qS hL).abelian.pullback T.hom),
        ((A.pullback T.hom).multiplication (2 * d) ≫ p.hom =
          (Over.pullback T.hom).map (inducingIsogeny A P L qS hL).hom) ∧
        p.HasPolarizationType δ ∧
        Nonempty (((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom T.hom)).sheaf ≅
          ((PoincareGraph.Bundles.poincareGraphBundle ((RationalProjectivePolarizationLocus.dualData A P L qS hL).pullback T.hom) p.hom).tensorPower d).sheaf) :=
  PolarizationParameter.RationalPolarizationLocus.parameter_hasPoint_iff
    (RationalProjectivePolarizationLocus.dualData A P L qS hL) (inducingIsogeny A P L qS hL) qS d hd P L δ hδ T

def universalIsogeny :
    Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (parameter A P L qS hL d hd δ hδ).hom)
      ((RationalProjectivePolarizationLocus.dualData A P L qS hL).abelian.pullback (parameter A P L qS hL d hd δ hδ).hom) :=
  PolarizationParameter.RationalPolarizationLocus.isogeny
    (RationalProjectivePolarizationLocus.dualData A P L qS hL) (inducingIsogeny A P L qS hL) qS d hd P L δ hδ

theorem universalIsogeny_division :
    (A.pullback (parameter A P L qS hL d hd δ hδ).hom).multiplication (2 * d) ≫
      (universalIsogeny A P L qS hL d hd δ hδ).hom =
        (Over.pullback (parameter A P L qS hL d hd δ hδ).hom).map
          (inducingIsogeny A P L qS hL).hom :=
  PolarizationParameter.RationalPolarizationLocus.isogeny_division
    (RationalProjectivePolarizationLocus.dualData A P L qS hL) (inducingIsogeny A P L qS hL) qS d hd P L δ hδ

theorem universalIsogeny_type :
    (universalIsogeny A P L qS hL d hd δ hδ).HasPolarizationType δ :=
  PolarizationParameter.RationalPolarizationLocus.isogeny_type
    (RationalProjectivePolarizationLocus.dualData A P L qS hL) (inducingIsogeny A P L qS hL) qS d hd P L δ hδ

def universalGraphPowerIso :
    ((A.zeroNormalizedBundle L).pullback
      (pullback.fst A.scheme.hom (parameter A P L qS hL d hd δ hδ).hom)).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle
        ((RationalProjectivePolarizationLocus.dualData A P L qS hL).pullback (parameter A P L qS hL d hd δ hδ).hom)
        (universalIsogeny A P L qS hL d hd δ hδ).hom).tensorPower d).sheaf :=
  PolarizationParameter.RationalPolarizationLocus.universalIso
    (RationalProjectivePolarizationLocus.dualData A P L qS hL) (inducingIsogeny A P L qS hL) qS d hd P L δ hδ

/-- The universal divisor has the original geometric-fiber positivity. -/
def polarization :
    PolarizationData.Polarization ((RationalProjectivePolarizationLocus.dualData A P L qS hL).pullback (parameter A P L qS hL d hd δ hδ).hom) δ :=
  PolarizationParameter.RationalPolarizationLocus.polarization
    (RationalProjectivePolarizationLocus.dualData A P L qS hL) (inducingIsogeny A P L qS hL) qS d hd P L δ hδ
    hL (inducingPoincareRecovery A P L qS hL)

def universalProjectivePresentation :
    Projective.ProjectivePresentations.ProjectivePresentation (A.pullback (parameter A P L qS hL d hd δ hδ).hom).scheme :=
  P.baseChange (parameter A P L qS hL d hd δ hδ).hom

/-- Keep the supplied original ordered full level by ordinary pullback. -/
def familyWithFullLevel {N : ℕ} (level : A.FullLevel N) :
    PolarizationData.PolarizedAbelianWithFullLevel g δ N (parameter A P L qS hL d hd δ hδ).left where
  abelian := A.pullback (parameter A P L qS hL d hd δ hδ).hom
  dual := (RationalProjectivePolarizationLocus.dualData A P L qS hL).pullback (parameter A P L qS hL d hd δ hδ).hom
  polarization := RationalProjectivePolarizationLocus.polarization A P L qS hL d hd δ hδ
  level := level.pullback (parameter A P L qS hL d hd δ hδ).hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.ProjectivePolarizationParameter.RationalProjectivePolarizationLocus

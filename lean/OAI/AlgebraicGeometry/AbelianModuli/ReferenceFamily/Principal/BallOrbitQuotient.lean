import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.BallDiffeomorphisms
import Mathlib.Topology.Algebra.ConstMulAction

/-! # Ball Orbit Quotient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The actual orbit relation in ReferenceFamily defines an open topological
quotient of its literal ball domain, with exactly the required fibers. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (N : ℕ)

instance Datum.RankThreePELDatum.principalBallAction_continuousConstSMul :
    ContinuousConstSMul (Groups.principalSpecialUnitary P.b P.lattice N) P.Domain where
  continuous_const_smul g := (P.principalBallAction_contMDiff N g).continuous

def Datum.RankThreePELDatum.principalOrbitSetoid : Setoid P.Domain :=
  MulAction.orbitRel (Groups.principalSpecialUnitary P.b P.lattice N) P.Domain

theorem Datum.RankThreePELDatum.principalOrbitSetoid_iff (z w : P.Domain) :
    (P.principalOrbitSetoid N).r z w ↔ P.OrbitRelation (Groups.principalSpecialUnitary P.b P.lattice N) z w := by
  change (∃ a : Groups.principalSpecialUnitary P.b P.lattice N, a • w = z) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    have hw : w = a⁻¹ • z := by rw [← ha, inv_smul_smul]
    exact ⟨a⁻¹, (a⁻¹).property, congrArg Subtype.val hw⟩
  · rintro ⟨a, ha, hw⟩
    let b : Groups.principalSpecialUnitary P.b P.lattice N := ⟨a, ha⟩
    have hb : w = b • z := Subtype.ext hw
    exact ⟨b⁻¹, hb ▸ inv_smul_smul b z⟩

def Datum.RankThreePELDatum.principalOrbitProjection : P.Domain → Quotient (P.principalOrbitSetoid N) := Quotient.mk _

theorem Datum.RankThreePELDatum.principalOrbitProjection_fibers (z w : P.Domain) :
    P.principalOrbitProjection N z = P.principalOrbitProjection N w ↔
      P.OrbitRelation (Groups.principalSpecialUnitary P.b P.lattice N) z w :=
  Quotient.eq.trans (P.principalOrbitSetoid_iff N z w)

theorem Datum.RankThreePELDatum.principalOrbitProjection_isOpenQuotientMap :
    IsOpenQuotientMap (P.principalOrbitProjection N) := MulAction.isOpenQuotientMap_quotientMk

instance Datum.RankThreePELDatum.principalOrbitQuotient_secondCountable : SecondCountableTopology (Quotient (P.principalOrbitSetoid N)) :=
  ContinuousConstSMul.secondCountableTopology

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

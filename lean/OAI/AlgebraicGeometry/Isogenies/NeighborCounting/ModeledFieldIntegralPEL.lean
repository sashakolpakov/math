import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldPEL
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralLieRanksQuotient

/-! # Modeled Field Integral PEL -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldIntegralPEL

noncomputable section

/-! The positive quotient is an actual object of the original integral
PEL moduli problem, with its signature transferred through the etale
isogeny. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldPEL
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralLieRanksQuotient

local instance fieldOverReduced {k : Type} [Field k] {S : Scheme.{0}}
    (b : Spec (.of k) ⟶ S) : IsReduced (Over.mk b).left :=
  inferInstanceAs (IsReduced (Spec (.of k)))

local instance fieldOverLocallyNoetherian {k : Type} [Field k] {S : Scheme.{0}}
    (b : Spec (.of k) ⟶ S) : IsLocallyNoetherian (Over.mk b).left :=
  inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))

variable {E k L R₀ : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field k] [Field L] [CommRing R₀] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iotaO : NumberField.RingOfIntegers E →+* R₀} {b : Spec (.of k) ⟶ Spec (.of R₀)}
  (A : PELModuli.IntegralModel.PEL.Has.IntegralPELObject P R₀ iotaO N (Over.mk b))
  (a : Spec (.of L) ⟶ Spec (.of k))
  (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.data.polarized.abelian.scheme (Over.mk a)) (R : F.Model)
  (n : ℕ) (hn : 0 < n)
  (Q : ModeledAbelian.Lifts.ModeledAbelianQuotient A.data.polarized.abelian (Over.mk a) F R n)
  (hdegree : n.Coprime ((∏ i, P.polarizationType i) ^ 2))
  (hF :
    let e := AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A.data.polarized.abelian A.data.polarized.dual
      A.data.polarized.polarization n hn
    let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.data.polarized.abelian.scheme n) F
    e.relativeAnnihilator H = H)
  (hlevel : n.Coprime N) (hstable : ∀ c, AbelianScheme.IsogenyQuotient.Action.Construction.RelativeSubgroupStable F (A.data.action.map c))

def modeledFieldIntegralPEL : PELModuli.IntegralModel.PEL.Has.IntegralPELObject P R₀ iotaO N (Over.mk (a ≫ b)) where
  data := ModeledFieldPEL.modeledFieldActionData A.data a F R n hn Q hdegree hF hlevel hstable
  rosati := ModeledFieldPEL.modeledFieldActionData_rosati A.data a F R n hn Q hdegree hF hlevel hstable A.rosati
  lieRanks := IntegralLieRanksQuotient.integralLieRanks_after_quotient P R₀ iotaO (Over.mk (a ≫ b))
    (A.data.polarized.abelian.pullback a) Q.target (A.data.action.pullback a)
    (Q.action A.data.action hstable) Q.isogeny (Q.action_projection A.data.action hstable)
    (PELModuli.IntegralModel.PEL.BaseChange.integralLieRanks_pullback A.data.polarized.abelian A.data.action A.lieRanks
      (Y := Over.mk (a ≫ b)) (Over.homMk a rfl))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldIntegralPEL

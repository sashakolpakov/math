import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Specialization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialEndEvaluation

/-! # Special End -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SpecialEnd.CM

noncomputable section

/-! Transporting the actual integral reduction back to the original
arithmetic Albanese gives precisely its already constructed source
specialization, including the integral point action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Specialization.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialEndEvaluation.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
  (hcop : Nat.Coprime q D.denominator)
  (res : AbelianScheme.TateComparison.Data.modelRing K D.denominator →+* ZMod q)
  (hres : res.comp (algebraMap (NumberField.RingOfIntegers K)
    (AbelianScheme.TateComparison.Data.modelRing K D.denominator)) = j.residue)

local notation "A" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D hg j hcop
local notation "G" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM.targetGroup D hg j hcop
local notation "H" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM.sourceGroup D res
local notation "e" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPolynomial.CM.comparisonIso D hg j hcop res hres

local instance : GrpObj (G).X := (G).grp
local instance : IsCommMonObj (G).X := (G).comm
local instance : GrpObj (H).X := (H).grp
local instance : IsCommMonObj (H).X := (H).comm
local instance : IsMonHom (e).hom := ComparisonPolynomial.CM.comparisonIso_group D hg j hcop res hres

def sourceData : SpecialEndEvaluation.CM.TransportedSpecialization.Data A H :=
  @SpecialEndEvaluation.CM.TransportedSpecialization.data K _ _ q _ _ A H e
    (ComparisonPolynomial.CM.comparisonIso_group D hg j hcop res hres)

theorem sourceData_specialization :
    (sourceData D hg j hcop res hres).specialization =
      Specialization.CM.sourceSpecialization D hg j hcop res hres := rfl

theorem sourceData_specialization_apply (f : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (A).variety.scheme) :
    (sourceData D hg j hcop res hres).specialization f =
      Specialization.CM.sourceSpecialization D hg j hcop res hres f :=
  congrArg (fun Φ => Φ f) (sourceData_specialization D hg j hcop res hres)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SpecialEnd.CM

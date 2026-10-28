import OAI.NumberTheory.PadicHodge.IntegralComparison.QuasicoherentTruncation
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.QuasiIso

/-! # Cohomology Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.CohomologyConcentration

noncomputable section

/-! If the cohomology sheaves of a quasicoherent complex are concentrated
in one degree, its actual ordered affine Čech total is computed by that
cohomology sheaf in the same degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

def homologyIso (n : ℕ) :
    ((OrderedCech.Total.Comparison.bicomplex π U K).total (.up ℕ)).homology n ≅
      ((OrderedCech.Total.Comparison.bicomplex π U
        ((HomologicalComplex.single X.Modules (.up ℕ) c).obj (K.homology c))).total (.up ℕ)).homology n := by
  have : ∀ q, ((CohomologyConcentration.truncation K c).X q).IsQuasicoherent :=
    QuasicoherentTruncation.truncation K c
  have : (K.homology c).IsQuasicoherent := QuasicoherentTruncation.cohomology K c
  have : ∀ q, (((HomologicalComplex.single X.Modules (.up ℕ) c).obj (K.homology c)).X q).IsQuasicoherent :=
    QuasicoherentTruncation.single (K.homology c) c
  have : QuasiIso (CohomologyConcentration.projection K c) :=
    CohomologyConcentration.projection_quasiIso K c hK
  have : QuasiIso (CohomologyConcentration.inclusion K c) :=
    CohomologyConcentration.inclusion_quasiIso K c hK
  have : QuasiIso (OrderedCech.QuasiIso.map π U (CohomologyConcentration.projection K c)) :=
    OrderedCech.QuasiIso.quasiIso π U _ hU
  have : QuasiIso (OrderedCech.QuasiIso.map π U (CohomologyConcentration.inclusion K c)) :=
    OrderedCech.QuasiIso.quasiIso π U _ hU
  exact isoOfQuasiIsoAt (OrderedCech.QuasiIso.map π U (CohomologyConcentration.projection K c)) n ≪≫
    (isoOfQuasiIsoAt (OrderedCech.QuasiIso.map π U (CohomologyConcentration.inclusion K c)) n).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.CohomologyConcentration

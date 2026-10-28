import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.CohomologyConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationNaturality

/-! # Concentration Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConcentrationNaturality

noncomputable section

/-! Naturality of the actual Čech-total comparison with a single
cohomology sheaf, before identifying the remaining degree shift. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationNaturality

variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))

def totalFunctor : CochainComplex X.Modules ℕ ⥤ CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ :=
  ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).mapHomologicalComplex (.up ℕ)) ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{u} Γ(S, ⊤)) (.up ℕ) (.up ℕ) (.up ℕ)

omit [X.IsSeparated] in
@[simp]
theorem totalFunctor_map {K L : CochainComplex X.Modules ℕ} (a : K ⟶ L) :
    (ConcentrationNaturality.totalFunctor π U).map a = OrderedCech.QuasiIso.map π U a := rfl

variable (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

include hU hK in
theorem projection_quasiIso : QuasiIso ((ConcentrationNaturality.totalFunctor π U).map (CohomologyConcentration.projection K c)) := by
  let (q : ℕ) : ((CohomologyConcentration.truncation K c).X q).IsQuasicoherent := QuasicoherentTruncation.truncation K c q
  let : QuasiIso (CohomologyConcentration.projection K c) := CohomologyConcentration.projection_quasiIso K c hK
  exact OrderedCech.QuasiIso.quasiIso π U (CohomologyConcentration.projection K c) hU

include hU hK in
theorem inclusion_quasiIso : QuasiIso ((ConcentrationNaturality.totalFunctor π U).map (CohomologyConcentration.inclusion K c)) := by
  let (q : ℕ) : ((CohomologyConcentration.truncation K c).X q).IsQuasicoherent := QuasicoherentTruncation.truncation K c q
  let : (K.homology c).IsQuasicoherent := QuasicoherentTruncation.cohomology K c
  let (q : ℕ) : (((HomologicalComplex.single X.Modules (.up ℕ) c).obj (K.homology c)).X q).IsQuasicoherent :=
    QuasicoherentTruncation.single (K.homology c) c q
  let : QuasiIso (CohomologyConcentration.inclusion K c) := CohomologyConcentration.inclusion_quasiIso K c hK
  exact OrderedCech.QuasiIso.quasiIso π U (CohomologyConcentration.inclusion K c) hU

variable {K} {L : CochainComplex X.Modules ℕ} [∀ q, (L.X q).IsQuasicoherent]
  (hL : ∀ q, q ≠ c → L.ExactAt q) (a : K ⟶ L)

@[reassoc]
theorem naturality (n : ℕ) :
    HomologicalComplex.homologyMap ((ConcentrationNaturality.totalFunctor π U).map a) n ≫
        (CohomologyConcentration.homologyIso π U hU L c hL n).hom =
      (CohomologyConcentration.homologyIso π U hU K c hK n).hom ≫
        HomologicalComplex.homologyMap ((ConcentrationNaturality.totalFunctor π U).map
          ((HomologicalComplex.single X.Modules (.up ℕ) c).map (HomologicalComplex.homologyMap a c))) n := by
  let F := ConcentrationNaturality.totalFunctor π U ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} Γ(S, ⊤)) (.up ℕ) n
  let : QuasiIso ((ConcentrationNaturality.totalFunctor π U).map (CohomologyConcentration.inclusion K c)) := inclusion_quasiIso π U hU K c hK
  let : QuasiIso ((ConcentrationNaturality.totalFunctor π U).map (CohomologyConcentration.inclusion L c)) := inclusion_quasiIso π U hU L c hL
  let iK := isoOfQuasiIsoAt ((ConcentrationNaturality.totalFunctor π U).map (CohomologyConcentration.inclusion K c)) n
  let iL := isoOfQuasiIsoAt ((ConcentrationNaturality.totalFunctor π U).map (CohomologyConcentration.inclusion L c)) n
  have hp := DualComplexHomology.map_square F _ _ _ _
    (HomologicalComplex.πTruncGE_naturality a (CohomologyConcentration.shift c)).symm
  have hi := DualComplexHomology.map_square F _ _ _ _ (CohomologyConcentrationNaturality.inclusion_naturality a c)
  have hi' := CohomologyConcentrationNaturality.inverse_square _ _ iK iL hi
  simpa only [CohomologyConcentration.homologyIso, Iso.trans_hom, Iso.symm_hom,
    isoOfQuasiIsoAt_hom, F, iK, iL, Functor.comp_map, HomologicalComplex.homologyFunctor_map,
    CohomologyConcentration.projection, Category.assoc, totalFunctor_map] using
    DualComplexHomology.compose_squares _ _ _ _ _ _ _ hp hi'

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConcentrationNaturality

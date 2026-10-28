import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechAdditiveCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConcentrationLocalRecovery

/-! # Ordered Cech Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCechConcentration

noncomputable section

/-! The canonical concentration on the original additive ordered Čech
complex agrees exactly with the scalar-forgotten native concentration. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic
variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))

abbrev functor (q : ℕ) := IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.totalFunctor U ⋙ homologyFunctor AddCommGrpCat.{u} (.up ℕ) q
abbrev nativeFunctor (q : ℕ) := Cech.ConcentrationNaturality.totalFunctor π U ⋙
  homologyFunctor (ModuleCat.{u} Γ(S, ⊤)) (.up ℕ) q

variable (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

include hU hK in
theorem projection_isIso (q : ℕ) : IsIso ((functor U q).map (CohomologyConcentration.projection K c)) := by
  let (k : ℕ) := QuasicoherentTruncation.truncation K c k
  let := CohomologyConcentration.projection_quasiIso K c hK
  let := IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.quasiIso (𝟙 X) U hU (CohomologyConcentration.projection K c)
  change IsIso (homologyMap ((IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.totalFunctor U).map (CohomologyConcentration.projection K c)) q)
  infer_instance

include hU hK in
theorem inclusion_isIso (q : ℕ) : IsIso ((functor U q).map (CohomologyConcentration.inclusion K c)) := by
  let (k : ℕ) := QuasicoherentTruncation.truncation K c k
  let := QuasicoherentTruncation.cohomology K c
  let (k : ℕ) := QuasicoherentTruncation.single (K.homology c) c k
  let := CohomologyConcentration.inclusion_quasiIso K c hK
  let := IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.quasiIso (𝟙 X) U hU (CohomologyConcentration.inclusion K c)
  change IsIso (homologyMap ((IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.totalFunctor U).map (CohomologyConcentration.inclusion K c)) q)
  infer_instance

def iso (q : ℕ) := by
  letI := projection_isIso U hU K c hK q
  letI := inclusion_isIso U hU K c hK q
  exact Functor.ConcentrationSingle.iso (functor U q) K c

theorem native_square (q : ℕ) :
    ((IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)).mapIso
      (Cech.CohomologyConcentration.homologyIso π U hU K c hK q)).hom ≫
        (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π U ((single X.Modules (.up ℕ) c).obj (K.homology c)) q).hom =
    (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π U K q).hom ≫ (iso U hU K c hK q).hom := by
  let := projection_isIso U hU K c hK q
  let := inclusion_isIso U hU K c hK q
  let := Cech.ConcentrationNaturality.projection_quasiIso π U hU K c hK
  let := Cech.ConcentrationNaturality.inclusion_quasiIso π U hU K c hK
  let : IsIso ((nativeFunctor π U q).map (CohomologyConcentration.projection K c)) := by
    change IsIso (homologyMap ((Cech.ConcentrationNaturality.totalFunctor π U).map (CohomologyConcentration.projection K c)) q)
    infer_instance
  let : IsIso ((nativeFunctor π U q).map (CohomologyConcentration.inclusion K c)) := by
    change IsIso (homologyMap ((Cech.ConcentrationNaturality.totalFunctor π U).map (CohomologyConcentration.inclusion K c)) q)
    infer_instance
  let F := nativeFunctor π U q ⋙ IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)
  let : IsIso (F.map (CohomologyConcentration.projection K c)) := by
    change IsIso ((IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)).map ((nativeFunctor π U q).map (CohomologyConcentration.projection K c)))
    infer_instance
  let : IsIso (F.map (CohomologyConcentration.inclusion K c)) := by
    change IsIso ((IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)).map ((nativeFunctor π U q).map (CohomologyConcentration.inclusion K c)))
    infer_instance
  have h := ConcentrationLocalRecovery.square F (functor U q) K c
    (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π U K q).hom (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π U (CohomologyConcentration.truncation K c) q).hom
    (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π U ((single X.Modules (.up ℕ) c).obj (K.homology c)) q).hom
    (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso_naturality π U (CohomologyConcentration.projection K c) q)
    (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso_naturality π U (CohomologyConcentration.inclusion K c) q)
  rw [← Functor.ConcentrationMap.iso_map] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCechConcentration

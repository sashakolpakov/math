import OAI.NumberTheory.PadicHodge.PeriodInvariants.BigEtaleCohomology
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantRestrictionCoherence
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ExtTransport

/-! # Big Etale Coherence -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.BigEtaleCoherence

noncomputable section

/-!
# Functoriality of rational pro-etale pullback

The canonical big-site pullbacks satisfy identity and composition.
The proved comparison equivalence transports these laws to the existing
small-site rational cohomology groups.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology OAI.NumberTheory.PadicHodge.PeriodInvariants.BigProEtaleSite OAI.NumberTheory.PadicHodge.PeriodInvariants.BigEtaleCohomology OAI.NumberTheory.PadicHodge.PeriodInvariants.ExtTransport
open OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantRestrictionCoherence

variable (p : ℕ) [Fact p.Prime]
variable {X Y Z : Scheme.{u}}

def pullbackFunctor_id (X : Scheme.{u}) : BigEtaleCohomology.pullbackFunctor p (𝟙 X) ≅ 𝟭 (BigProEtaleSite.BigSheaf p X) :=
  Functor.sheafPushforwardContinuousId' (Over.mapId X)
    (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) (Scheme.proetaleTopology.over X)

def pullbackFunctor_comp (g : X ⟶ Y) (h : Y ⟶ Z) :
    BigEtaleCohomology.pullbackFunctor p h ⋙ BigEtaleCohomology.pullbackFunctor p g ≅ BigEtaleCohomology.pullbackFunctor p (g ≫ h) := by
  letI := Functor.isContinuous_comp (Over.map g) (Over.map h)
    (Scheme.proetaleTopology.over X) (Scheme.proetaleTopology.over Y) (Scheme.proetaleTopology.over Z)
  exact Functor.sheafPushforwardContinuousIso (Over.mapComp g h).symm
    (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) (Scheme.proetaleTopology.over X) (Scheme.proetaleTopology.over Z)

theorem constantTransport_id (X : Scheme.{u}) : BigEtaleCohomology.constantTransport p (𝟙 X) =
    (pullbackFunctor_id p X).app (BigProEtaleSite.constantUnit p X) := by
  have hn := ConstantRestrictionCoherence.transport_natIso (Scheme.proetaleTopology.over X) (Scheme.proetaleTopology.over X)
    (Over.map (𝟙 X)) (Over.mapId X) (ModuleCat.of (IntegralComparison.Cohomology.Coeff.{u} p) (IntegralComparison.Cohomology.Coeff.{u} p))
  rw [ConstantRestrictionCoherence.transport_id] at hn
  exact hn

theorem constantTransport_comp (g : X ⟶ Y) (h : Y ⟶ Z) :
    (BigEtaleCohomology.pullbackFunctor p g).mapIso (BigEtaleCohomology.constantTransport p h) ≪≫ BigEtaleCohomology.constantTransport p g =
      (pullbackFunctor_comp p g h).app (BigProEtaleSite.constantUnit p Z) ≪≫ BigEtaleCohomology.constantTransport p (g ≫ h) := by
  let := Functor.isContinuous_comp (Over.map g) (Over.map h)
    (Scheme.proetaleTopology.over X) (Scheme.proetaleTopology.over Y) (Scheme.proetaleTopology.over Z)
  let := isCocontinuous_comp (Over.map g) (Over.map h)
    (Scheme.proetaleTopology.over X) (Scheme.proetaleTopology.over Y)
    (L := Scheme.proetaleTopology.over Z)
  exact (ConstantRestrictionCoherence.transport_comp (Scheme.proetaleTopology.over X) (Scheme.proetaleTopology.over Y)
    (Scheme.proetaleTopology.over Z) (Over.map g) (Over.map h)
      (ModuleCat.of (IntegralComparison.Cohomology.Coeff.{u} p) (IntegralComparison.Cohomology.Coeff.{u} p))).trans
    (ConstantRestrictionCoherence.transport_natIso (Scheme.proetaleTopology.over X) (Scheme.proetaleTopology.over Z)
      (Over.map g ⋙ Over.map h) (Over.mapComp g h).symm
        (ModuleCat.of (IntegralComparison.Cohomology.Coeff.{u} p) (IntegralComparison.Cohomology.Coeff.{u} p)))

theorem coefficientTransport_id (X : Scheme.{u}) : BigEtaleCohomology.coefficientTransport p (𝟙 X) =
    (pullbackFunctor_id p X).app (BigEtaleCohomology.coefficientSheaf p X) := by
  apply Iso.ext
  ext U a
  rfl

theorem coefficientTransport_comp (g : X ⟶ Y) (h : Y ⟶ Z) :
    (BigEtaleCohomology.pullbackFunctor p g).mapIso (BigEtaleCohomology.coefficientTransport p h) ≪≫ BigEtaleCohomology.coefficientTransport p g =
      (pullbackFunctor_comp p g h).app (BigEtaleCohomology.coefficientSheaf p Z) ≪≫ BigEtaleCohomology.coefficientTransport p (g ≫ h) := by
  apply Iso.ext
  ext U a
  rfl

theorem bigPullback_id (X : Scheme.{u}) (n : ℕ) (x : BigEtaleCohomology.Cohomology p X n) :
    BigEtaleCohomology.bigPullback p (𝟙 X) n x = x := by
  change ExtTransport.exactTransport (IntegralComparison.Cohomology.Coeff.{u} p) (BigEtaleCohomology.pullbackFunctor p (𝟙 X))
    (BigEtaleCohomology.constantTransport p (𝟙 X)) (BigEtaleCohomology.coefficientTransport p (𝟙 X)) n x = x
  rw [constantTransport_id, coefficientTransport_id]
  have hn := ExtTransport.exactTransport_natIso (IntegralComparison.Cohomology.Coeff.{u} p) (pullbackFunctor_id p X)
    (Iso.refl (BigProEtaleSite.constantUnit p X)) (Iso.refl (BigEtaleCohomology.coefficientSheaf p X)) x
  have ht := congrArg₂ (fun iA iB => ExtTransport.exactTransport (IntegralComparison.Cohomology.Coeff.{u} p)
    (BigEtaleCohomology.pullbackFunctor p (𝟙 X)) iA iB n x)
    (Iso.trans_refl ((pullbackFunctor_id p X).app (BigProEtaleSite.constantUnit p X))).symm
    (Iso.trans_refl ((pullbackFunctor_id p X).app (BigEtaleCohomology.coefficientSheaf p X))).symm
  exact ht.trans (hn.trans (ExtTransport.exactTransport_id (IntegralComparison.Cohomology.Coeff.{u} p) x))

theorem bigPullback_comp (g : X ⟶ Y) (h : Y ⟶ Z) (n : ℕ) (x : BigEtaleCohomology.Cohomology p Z n) :
    BigEtaleCohomology.bigPullback p g n (BigEtaleCohomology.bigPullback p h n x) = BigEtaleCohomology.bigPullback p (g ≫ h) n x := by
  change ExtTransport.exactTransport (IntegralComparison.Cohomology.Coeff.{u} p) (BigEtaleCohomology.pullbackFunctor p g) (BigEtaleCohomology.constantTransport p g)
    (BigEtaleCohomology.coefficientTransport p g) n
    (ExtTransport.exactTransport (IntegralComparison.Cohomology.Coeff.{u} p) (BigEtaleCohomology.pullbackFunctor p h) (BigEtaleCohomology.constantTransport p h)
      (BigEtaleCohomology.coefficientTransport p h) n x) =
    ExtTransport.exactTransport (IntegralComparison.Cohomology.Coeff.{u} p) (BigEtaleCohomology.pullbackFunctor p (g ≫ h)) (BigEtaleCohomology.constantTransport p (g ≫ h))
      (BigEtaleCohomology.coefficientTransport p (g ≫ h)) n x
  rw [ExtTransport.exactTransport_comp, constantTransport_comp, coefficientTransport_comp]
  exact ExtTransport.exactTransport_natIso (IntegralComparison.Cohomology.Coeff.{u} p) (pullbackFunctor_comp p g h)
    (BigEtaleCohomology.constantTransport p (g ≫ h)) (BigEtaleCohomology.coefficientTransport p (g ≫ h)) x

theorem pullback_id (X : Scheme.{u}) (n : ℕ) (x : IntegralComparison.Cohomology.RationalEllAdicCohomology p X n) :
    BigEtaleCohomology.pullback p (𝟙 X) n x = x := by
  change BigEtaleCohomology.comparisonEquiv p X n (BigEtaleCohomology.bigPullback p (𝟙 X) n ((BigEtaleCohomology.comparisonEquiv p X n).symm x)) = x
  rw [bigPullback_id, LinearEquiv.apply_symm_apply]

theorem pullback_comp (g : X ⟶ Y) (h : Y ⟶ Z) (n : ℕ) (x : IntegralComparison.Cohomology.RationalEllAdicCohomology p Z n) :
    BigEtaleCohomology.pullback p g n (BigEtaleCohomology.pullback p h n x) = BigEtaleCohomology.pullback p (g ≫ h) n x := by
  change BigEtaleCohomology.comparisonEquiv p X n (BigEtaleCohomology.bigPullback p g n ((BigEtaleCohomology.comparisonEquiv p Y n).symm
    (BigEtaleCohomology.comparisonEquiv p Y n (BigEtaleCohomology.bigPullback p h n ((BigEtaleCohomology.comparisonEquiv p Z n).symm x))))) =
    BigEtaleCohomology.comparisonEquiv p X n (BigEtaleCohomology.bigPullback p (g ≫ h) n ((BigEtaleCohomology.comparisonEquiv p Z n).symm x))
  rw [LinearEquiv.symm_apply_apply, bigPullback_comp]

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.BigEtaleCoherence

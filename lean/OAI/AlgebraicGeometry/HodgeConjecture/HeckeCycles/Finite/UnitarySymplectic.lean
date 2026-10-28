import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FiniteSymplectic
import OAI.RepresentationTheory.Theta.Adelic.RationalSU
import OAI.RepresentationTheory.Weil.AdelicSplitting.BaseChange

/-! # Unitary Symplectic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.UnitarySymplectic.CM

noncomputable section

/-! The normalized finite unitary action has an actual assembled
symplectic projection over the number-field finite adeles. -/

open scoped Classical _root_.NumberField
open Filter OAI.RepresentationTheory.Weil.AdelicSplitting.BaseChange.Construction
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU

variable (F : Type) [Field F] [NumberField F] (d : F) (n m : ℕ)
  (H : (Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
  (hd : d ≠ 0) (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K)
  (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

def localHom (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)) →*
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Symplectic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) :=
  (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localDualAction F d n m H K P (.inr v)).comp (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUToPair F H K (.inr v)).toMonoidHom

include D in
theorem local_integral : ∀ᶠ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F in cofinite,
    Set.MapsTo (localHom F d n m H K P v) (RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr v))
      (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.symplecticIntegral F (n * m) (.inr v)) := by
  have h := Sum.inr_injective.tendsto_cofinite.eventually (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localAction_integral F d n m H K hd C P D)
  filter_upwards [h] with v hv
  intro g hg
  exact hv ⟨hg, (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localUnitaryIntegral F K.val (.inr v)).one_mem⟩

def restricted : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H →* HeckeCycles.NumberField.FiniteSymplectic.CM.Group F (n * m) :=
  RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.restrictedMap (fun v => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr v))
    (fun v => RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.symplecticIntegral F (n * m) (.inr v))
    (localHom F d n m H K P) (local_integral F d n m H K hd C P D)

def assembled : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin (n * m)) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :=
  (HeckeCycles.NumberField.FiniteSymplectic.CM.assemble F (n * m)).comp (restricted F d n m H K hd C P D)

theorem assembled_local (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H) (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (HeckeCycles.NumberField.FiniteSymplectic.CM.evaluation F v)
      (assembled F d n m H K hd C P D g) = localHom F d n m H K P v (g v) :=
  HeckeCycles.NumberField.FiniteSymplectic.CM.assemble_evaluation F (n * m) _ v

theorem local_rational (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val) :
    localHom F d n m H K P v (RepresentationTheory.Theta.Adelic.RationalSU.rationalLocalSU F H (.inr v) g) =
      RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.rationalSymplecticLocal F (n * m) (.inr v)
        (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary H.val g, 1)) := by
  change RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localDualAction F d n m H K P (.inr v)
    (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUToPair F H K (.inr v) (RepresentationTheory.Theta.Adelic.RationalSU.rationalLocalSU F H (.inr v) g)) = _
  have he : RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUToPair F H K (.inr v) (RepresentationTheory.Theta.Adelic.RationalSU.rationalLocalSU F H (.inr v) g) =
      RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalPairLocal F H.val K.val (.inr v) (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary H.val g, 1) := by
    apply Prod.ext
    · rfl
    · exact (map_one (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal F K.val (.inr v))).symm
  rw [he, RepresentationTheory.Weil.AdelicSplitting.BaseChange.Construction.localDualAction_rational]

theorem assembled_rational (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val) :
    assembled F d n m H K hd C P D (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU F H g) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F))
        (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary H.val g, 1)) := by
  apply Subtype.ext
  apply HeckeCycles.NumberField.FiniteSymplectic.CM.matrix_ext F
  intro v
  have h := congrArg Subtype.val
    ((assembled_local F d n m H K hd C P D (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU F H g) v).trans
      (local_rational F d n m H K P v g))
  exact h.trans (by
    change _ = ((RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary H.val g, 1)).val.map
      (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F))).map (HeckeCycles.NumberField.FiniteSymplectic.CM.evaluation F v)
    rw [Matrix.map_map]
    rfl)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.UnitarySymplectic.CM

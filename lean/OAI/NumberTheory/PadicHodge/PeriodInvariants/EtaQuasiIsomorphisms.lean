import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCohomologyNaturality
import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaDegreeZero
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ZeroDifferentialHomologyMaps

/-! # Eta Quasi Isomorphisms -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaQuasiIsomorphisms

noncomputable section

/-!
# Eta preserves quasi-isomorphisms of scalar-torsion-free complexes

The degree-zero inclusion is a quasi-isomorphism without any regularity
assumption. The positive-degree quotient calculation then proves the
claim for every nonnegative degree of termwise scalar-torsion-free
complexes, using the actual induced cochain map.
-/

universe u v

open _root_.CategoryTheory OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaComplex OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCycles OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaDegreeZero
  ModuleHomologyMaps ZeroDifferentialHomologyMaps EtaCohomologyNaturality

variable {R : Type u} [CommRing R] (a : R)
  {C D : CochainComplex (ModuleCat.{v} R) ℕ} (f : C ⟶ D)

def zeroShortMap : C.sc' 0 0 1 ⟶ D.sc' 0 0 1 :=
  (HomologicalComplex.shortComplexFunctor' _ _ 0 0 1).map f

theorem quasiIsoAt_zero_iff : QuasiIsoAt f 0 ↔ Function.Bijective (ModuleHomologyMaps.cycleMap (zeroShortMap f)) :=
  (CochainComplex.quasiIsoAt₀_iff f).trans
    (ZeroDifferentialHomologyMaps.quasiIso_iff_cycleMap_bijective (zeroShortMap f)
      (by change C.d 0 0 = 0; simp) (by change D.d 0 0 = 0; simp))

theorem inclusion_cycleMap_bijective (C : CochainComplex (ModuleCat.{v} R) ℕ) :
    Function.Bijective (ModuleHomologyMaps.cycleMap (zeroShortMap (EtaComplex.inclusion a C))) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker (C.d 0 1).hom => z.val) h
  · intro x
    refine ⟨(EtaDegreeZero.etaCyclesEquiv a C 0).symm (EtaCycles.scaleCycles a C 0 x), ?_⟩
    apply Subtype.ext
    change a ^ 0 • (x.val : C.X 0) = (x.val : C.X 0)
    rw [pow_zero, one_smul]

theorem inclusion_quasiIsoAt_zero (C : CochainComplex (ModuleCat.{v} R) ℕ) :
    QuasiIsoAt (EtaComplex.inclusion a C) 0 :=
  (quasiIsoAt_zero_iff (EtaComplex.inclusion a C)).mpr (inclusion_cycleMap_bijective a C)

theorem eta_quasiIsoAt_zero [QuasiIsoAt f 0] : QuasiIsoAt (EtaComplex.etaMap a f) 0 := by
  let _ := inclusion_quasiIsoAt_zero a C
  let _ := inclusion_quasiIsoAt_zero a D
  have hcomp : QuasiIsoAt (EtaComplex.etaMap a f ≫ EtaComplex.inclusion a D) 0 := by
    rw [EtaComplex.inclusion_natural]
    infer_instance
  exact quasiIsoAt_of_comp_right (EtaComplex.etaMap a f) (EtaComplex.inclusion a D) 0

theorem etaMap_quasiIso (hC : ∀ n, IsSMulRegular (C.X n) a)
    (hD : ∀ n, IsSMulRegular (D.X n) a) [QuasiIso f] : QuasiIso (EtaComplex.etaMap a f) where
  quasiIsoAt n := by
    cases n with
    | zero => exact eta_quasiIsoAt_zero a f
    | succ n =>
      exact EtaCohomologyNaturality.eta_quasiIsoAt_succ a f n
        (hC (n + 1)) (hC (n + 1 + 1)) (hD (n + 1)) (hD (n + 1 + 1))

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaQuasiIsomorphisms

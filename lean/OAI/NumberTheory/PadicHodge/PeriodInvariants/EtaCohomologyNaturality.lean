import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaConcreteHomology
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ModuleHomologyMaps
import OAI.NumberTheory.PadicHodge.PeriodInvariants.TorsionQuotientDescent

/-! # Eta Cohomology Naturality -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCohomologyNaturality

noncomputable section

/-!
# Naturality of the eta cohomology quotient

The quotient description commutes with every cochain map. Hence a map
which is bijective on original cohomology is bijective on eta cohomology
when the relevant terms are scalar-torsion free.
-/

universe u v

open _root_.CategoryTheory OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaComplex OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCycles OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaBoundaries
  EtaCohomology EtaConcreteHomology.Concrete ModuleHomologyMaps

variable {R : Type u} [CommRing R] (a : R)
  {C D : CochainComplex (ModuleCat.{v} R) ℕ} (f : C ⟶ D)

def originalShortMap (n : ℕ) : C.sc' n (n + 1) (n + 1 + 1) ⟶ D.sc' n (n + 1) (n + 1 + 1) :=
  (HomologicalComplex.shortComplexFunctor' _ _ n (n + 1) (n + 1 + 1)).map f

def originalMap (n : ℕ) : EtaCohomology.cohomology C n →ₗ[R] EtaCohomology.cohomology D n :=
  ModuleHomologyMaps.quotientMap (originalShortMap f n)

def etaShortMap (n : ℕ) : EtaConcreteHomology.Concrete.etaShortComplex a C n ⟶ EtaConcreteHomology.Concrete.etaShortComplex a D n where
  τ₁ := ModuleCat.ofHom (EtaComplex.componentMap a f n)
  τ₂ := ModuleCat.ofHom (EtaComplex.componentMap a f (n + 1))
  τ₃ := ModuleCat.ofHom (EtaComplex.componentMap a f (n + 1 + 1))
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun h : C.X n ⟶ D.X (n + 1) => h (x : EtaComplex.term a C n).val)
      (f.comm n (n + 1))
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun h : C.X (n + 1) ⟶ D.X (n + 1 + 1) =>
      h (x : EtaComplex.term a C (n + 1)).val) (f.comm (n + 1) (n + 1 + 1))

def etaMapHomology (n : ℕ) : EtaCohomology.etaCohomology a C n →ₗ[R] EtaCohomology.etaCohomology a D n :=
  ModuleHomologyMaps.quotientMap (etaShortMap a f n)

theorem compare_natural (n : ℕ) (hC : IsSMulRegular (C.X (n + 1)) a)
    (hD : IsSMulRegular (D.X (n + 1)) a) :
    (etaMapHomology a f n).comp (EtaCohomology.compare a C n hC) =
      (EtaCohomology.compare a D n hD).comp (originalMap f n) := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on (LinearMap.range (EtaBoundaries.toCycles C n)) x ?_
  intro z
  change (Submodule.Quotient.mk
    (ModuleHomologyMaps.cycleMap (etaShortMap a f n) (EtaCycles.scaleCycles a C (n + 1) z)) : EtaCohomology.etaCohomology a D n) =
    Submodule.Quotient.mk (EtaCycles.scaleCycles a D (n + 1) (ModuleHomologyMaps.cycleMap (originalShortMap f n) z))
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  apply Subtype.ext
  exact (f.f (n + 1)).hom.map_smul (a ^ (n + 1)) (z : C.X (n + 1))

theorem etaMapHomology_bijective (n : ℕ)
    (hC : IsSMulRegular (C.X (n + 1)) a) (hC' : IsSMulRegular (C.X (n + 1 + 1)) a)
    (hD : IsSMulRegular (D.X (n + 1)) a) (hD' : IsSMulRegular (D.X (n + 1 + 1)) a)
    (hf : Function.Bijective (originalMap f n)) : Function.Bijective (etaMapHomology a f n) :=
  TorsionQuotientDescent.bijective a (EtaCohomology.compare a C n hC) (EtaCohomology.compare a D n hD)
    (EtaCohomology.compare_surjective a C n hC hC') (EtaCohomology.compare_surjective a D n hD hD')
    (EtaCohomology.compare_eq_zero_iff a C n hC) (EtaCohomology.compare_eq_zero_iff a D n hD)
    (originalMap f n) (etaMapHomology a f n) hf (compare_natural a f n hC hD)

theorem original_quasiIsoAt_iff (n : ℕ) :
    QuasiIsoAt f (n + 1) ↔ Function.Bijective (originalMap f n) :=
  (quasiIsoAt_iff' f n (n + 1) (n + 1 + 1) (by simp) (by simp)).trans
    (ModuleHomologyMaps.quasiIso_iff_bijective (originalShortMap f n))

theorem etaShortComplexIso_natural (n : ℕ) :
    originalShortMap (EtaComplex.etaMap a f) n ≫ (EtaConcreteHomology.Concrete.etaShortComplexIso a D n).hom =
      (EtaConcreteHomology.Concrete.etaShortComplexIso a C n).hom ≫ etaShortMap a f n := by
  ext <;> rfl

theorem eta_quasiIsoAt_iff (n : ℕ) :
    QuasiIsoAt (EtaComplex.etaMap a f) (n + 1) ↔ Function.Bijective (etaMapHomology a f n) :=
  (quasiIsoAt_iff' (EtaComplex.etaMap a f) n (n + 1) (n + 1 + 1) (by simp) (by simp)).trans
    ((ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (EtaConcreteHomology.Concrete.etaShortComplexIso a C n) (EtaConcreteHomology.Concrete.etaShortComplexIso a D n)
        (etaShortComplexIso_natural a f n).symm)).trans
      (ModuleHomologyMaps.quasiIso_iff_bijective (etaShortMap a f n)))

theorem eta_quasiIsoAt_succ (n : ℕ)
    (hC : IsSMulRegular (C.X (n + 1)) a) (hC' : IsSMulRegular (C.X (n + 1 + 1)) a)
    (hD : IsSMulRegular (D.X (n + 1)) a) (hD' : IsSMulRegular (D.X (n + 1 + 1)) a)
    [QuasiIsoAt f (n + 1)] : QuasiIsoAt (EtaComplex.etaMap a f) (n + 1) :=
  (eta_quasiIsoAt_iff a f n).mpr (etaMapHomology_bijective a f n hC hC' hD hD'
    ((original_quasiIsoAt_iff f n).mp inferInstance))

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCohomologyNaturality

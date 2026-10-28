import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoordinateBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopCycleBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DeterminantTransition

/-! # Purity Localization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.PurityLocalization

noncomputable section

/-! The normalized top purity map for the actual exterior Koszul resolution
commutes with flat scalar extension of the original equations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

open OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology OAI.NumberTheory.PadicHodge.IntegralComparison.TopHomologyCokernel

abbrev tensorFunctor := FlatBaseChange.tensorFunctor R S

def complexIso {n : ℕ} (s : Fin n → R) :
    ((tensorFunctor R S).mapHomologicalComplex (.up ℕ)).obj (OrientedTopCohomology.dualComplex R s) ≅
      OrientedTopCohomology.dualComplex S (algebraMap R S ∘ s) := by
  letI (i : ℕ) : Module.Free R ((OrientedTopCohomology.koszul R s).X i) :=
    inferInstanceAs (Module.Free R (⋀[R]^i (Fin n → R)))
  letI (i : ℕ) : Module.Finite R ((OrientedTopCohomology.koszul R s).X i) :=
    inferInstanceAs (Module.Finite R (⋀[R]^i (Fin n → R)))
  exact IntegralComparison.Finite.FreeDualBaseChange.complexIso R S (OrientedTopCohomology.koszul R s) ≪≫
    DualFlatBaseChange.dualIso S (CoordinateBaseChange.iso R S s)

def component {n : ℕ} (s : Fin n → R) (i : ℕ) :
    S ⊗[R] Module.Dual R (⋀[R]^i (Fin n → R)) →ₗ[S]
      Module.Dual S (⋀[S]^i (Fin n → S)) :=
  ((complexIso R S s).hom.f i).hom

theorem component_top {n : ℕ} (s : Fin n → R)
    (a : S) (f : Module.Dual R (⋀[R]^n (Fin n → R))) :
    component R S s n (a ⊗ₜ[R] f)
        (TopExteriorCoordinates.generator (Pi.basisFun S (Fin n))) =
      a * algebraMap R S (f (TopExteriorCoordinates.generator (Pi.basisFun R (Fin n)))) := by
  change IntegralComparison.Finite.FreeDualBaseChange.equiv R S (⋀[R]^n (Fin n → R)) (a ⊗ₜ[R] f)
    ((CoordinateBaseChange.iso R S s).inv.f n
      (TopExteriorCoordinates.generator (Pi.basisFun S (Fin n)))) = _
  have h : (CoordinateBaseChange.iso R S s).inv.f n
      (TopExteriorCoordinates.generator (Pi.basisFun S (Fin n))) =
        1 ⊗ₜ[R] TopExteriorCoordinates.generator (Pi.basisFun R (Fin n)) := by
    rw [← CoordinateBaseChange.iso_top_generator R S s]
    exact ConcreteCategory.congr_hom
      (congrArg (fun k => k.f n) (CoordinateBaseChange.iso R S s).hom_inv_id) _
  rw [h, IntegralComparison.Finite.FreeDualBaseChange.equiv_tmul_one]

def homologyIso {n : ℕ} (s : Fin n → R) :
    (tensorFunctor R S).obj ((OrientedTopCohomology.dualComplex R s).homology n) ≅
      (OrientedTopCohomology.dualComplex S (algebraMap R S ∘ s)).homology n :=
  (((OrientedTopCohomology.dualComplex R s).sc n).mapHomologyIso (tensorFunctor R S)).symm ≪≫
    homologyMapIso (complexIso R S s) n

theorem cycleClass_homologyIso {n : ℕ} (s : Fin n → R) :
    (tensorFunctor R S).map (TopHomologyCokernel.cycleClass (OrientedTopCohomology.dualComplex R s) n (OrientedTopCohomology.outgoing_isZero R s)) ≫
        (homologyIso R S s).hom =
      (complexIso R S s).hom.f n ≫
        TopHomologyCokernel.cycleClass (OrientedTopCohomology.dualComplex S (algebraMap R S ∘ s)) n
          (OrientedTopCohomology.outgoing_isZero S (algebraMap R S ∘ s)) := by
  let F := tensorFunctor R S
  have hF := F.map_isZero (OrientedTopCohomology.outgoing_isZero R s)
  have h := TopCycleBaseChange.cycleClass_map F (OrientedTopCohomology.dualComplex R s) n
    (OrientedTopCohomology.outgoing_isZero R s) hF
  have hc : F.map (TopHomologyCokernel.cycleClass (OrientedTopCohomology.dualComplex R s) n (OrientedTopCohomology.outgoing_isZero R s)) ≫
      (((OrientedTopCohomology.dualComplex R s).sc n).mapHomologyIso F).inv =
        TopHomologyCokernel.cycleClass ((F.mapHomologicalComplex (.up ℕ)).obj (OrientedTopCohomology.dualComplex R s)) n hF := by
    rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  dsimp only [homologyIso, Iso.trans_hom, Iso.symm_hom, homologyMapIso_hom]
  rw [← Category.assoc, hc]
  exact DeterminantTransition.cycleClass_naturality (complexIso R S s).hom n hF _

theorem cycleClass_purity {n : ℕ} (s : Fin n → R) (a : S)
    (f : Module.Dual R (⋀[R]^n (Fin n → R))) :
    (OrientedTopCohomology.iso S (algebraMap R S ∘ s)).hom
      ((homologyIso R S s).hom
        (a ⊗ₜ[R] TopHomologyCokernel.cycleClass (OrientedTopCohomology.dualComplex R s) n (OrientedTopCohomology.outgoing_isZero R s) f)) =
      Ideal.Quotient.mk (OrientedTopCohomology.ideal S (algebraMap R S ∘ s))
        (a * algebraMap R S (f (TopExteriorCoordinates.generator (Pi.basisFun R (Fin n))))) := by
  have h := congrArg (fun k => k ≫ (OrientedTopCohomology.iso S
      (algebraMap R S ∘ s)).hom) (cycleClass_homologyIso R S s)
  rw [Category.assoc, Category.assoc, OrientedTopCohomology.cycleClass_iso] at h
  have hx := ConcreteCategory.congr_hom h (a ⊗ₜ[R] f)
  change _ = (OrientedTopCohomology.ideal S (algebraMap R S ∘ s)).mkQ
    (component R S s n (a ⊗ₜ[R] f)
      (TopExteriorCoordinates.generator (Pi.basisFun S (Fin n)))) at hx
  rw [component_top] at hx
  exact hx

def quotientMap {n : ℕ} (s : Fin n → R) :
    (R ⧸ OrientedTopCohomology.ideal R s) →+* (S ⧸ OrientedTopCohomology.ideal S (algebraMap R S ∘ s)) :=
  Ideal.quotientMap _ (algebraMap R S) (by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨i, rfl⟩)

theorem purity {n : ℕ} (s : Fin n → R) (a : S) (x : (OrientedTopCohomology.dualComplex R s).homology n) :
    (OrientedTopCohomology.iso S (algebraMap R S ∘ s)).hom
        ((homologyIso R S s).hom (a ⊗ₜ[R] x)) =
      a • PurityLocalization.quotientMap R S s ((OrientedTopCohomology.iso R s).hom x) := by
  let cl := TopHomologyCokernel.cycleClass (OrientedTopCohomology.dualComplex R s) n (OrientedTopCohomology.outgoing_isZero R s)
  let : Epi cl := by
    dsimp only [cl, TopHomologyCokernel.cycleClass, TopHomologyCokernel.shortClass]
    infer_instance
  obtain ⟨f, rfl⟩ := (ModuleCat.epi_iff_surjective cl).mp inferInstance x
  change Module.Dual R (⋀[R]^n (Fin n → R)) at f
  rw [cycleClass_purity]
  have hc := ConcreteCategory.congr_hom (OrientedTopCohomology.cycleClass_iso R s) f
  change (OrientedTopCohomology.iso R s).hom (cl f) =
    Ideal.Quotient.mk (OrientedTopCohomology.ideal R s)
      (f (TopExteriorCoordinates.generator (Pi.basisFun R (Fin n)))) at hc
  rw [hc]
  simp [PurityLocalization.quotientMap, map_mul, Algebra.smul_def]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.PurityLocalization

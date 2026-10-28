import OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex
import OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant

/-! # Schrodinger Reindex -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SchrodingerReindex.CM.Intertwiner

/-! Heisenberg covariance transports through actual coordinate
relabeling of the test functions and symplectic phase space. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
variable {I J K : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [CommRing K] [Algebra ℚ K] [TopologicalSpace K]

omit [Algebra ℚ K] in
theorem phase_left (e : I ≃ J) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp J K) (p q : I → K) :
    RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e (fun i => ((RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e.symm g).val *ᵥ Sum.elim p q) (Sum.inl i)) =
      fun j => (g.val *ᵥ Sum.elim (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e p) (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e q)) (Sum.inl j) := by
  have h := RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex_inverse_action e g (Sum.elim p q)
  rw [RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex_sum_elim] at h
  exact congrArg (fun v : J ⊕ J → K => fun j => v (Sum.inl j)) h

omit [Algebra ℚ K] in
theorem phase_right (e : I ≃ J) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp J K) (p q : I → K) :
    RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e (fun i => ((RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e.symm g).val *ᵥ Sum.elim p q) (Sum.inr i)) =
      fun j => (g.val *ᵥ Sum.elim (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e p) (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e q)) (Sum.inr j) := by
  have h := RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex_inverse_action e g (Sum.elim p q)
  rw [RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex_sum_elim] at h
  exact congrArg (fun v : J ⊕ J → K => fun j => v (Sum.inr j)) h

theorem intertwines (e : I ≃ J)
    (S : Submodule ℂ ((I → K) → ℂ)) (T : Submodule ℂ ((J → K) → ℂ)) (E : S ≃ₗ[ℂ] T)
    (hE : ∀ f : S, ∀ y : J → K, (E f).val y = f.val (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm y))
    (hEi : ∀ f : T, ∀ x : I → K, (E.symm f).val x = f.val (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e x))
    (ψ : AddChar K ℂ) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp J K) (U : T ≃ₗ[ℂ] T)
    (hU : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg ψ T g U) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg ψ S (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e.symm g) (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.conjugateLinearAut E.symm U) := by
  intro p q f h hh x
  have hfval : (E f).val = fun y => f.val (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm y) := funext (hE f)
  have hin : ∀ y, (E h).val y =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg ψ (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e p) (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e q) (E f).val y := by
    intro y
    rw [hE, hh, hfval]
    exact RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.heisenberg_positionReindex e ψ p q f.val y
  have hout := hU (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e p) (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e q) (E f) (E h) hin (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e x)
  rw [← phase_left e g p q, ← phase_right e g p q, RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.heisenberg_positionReindex_forward] at hout
  have hfun : (fun y => (U (E f)).val (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e y)) = (E.symm (U (E f))).val :=
    (funext (hEi (U (E f)))).symm
  rw [hfun] at hout
  change (E.symm (U (E h))).val x = _
  rw [hEi]
  exact hout

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SchrodingerReindex.CM.Intertwiner

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SchrodingerReindex.CM

/-! Transport a genuine Schrödinger cover through proved coordinate,
test-function, and Haar-pairing identifications. -/

open scoped Classical _root_.Matrix
open _root_.Matrix _root_.MeasureTheory
variable {I J K : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [CommRing K] [Algebra ℚ K] [TopologicalSpace K] [MeasurableSpace K]

omit [Algebra ℚ K] [TopologicalSpace K] [MeasurableSpace K] in
theorem symplectic_injective (e : I ≃ J) : Function.Injective (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e (K := K)) := by
  intro g h he
  have hh := congrArg (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e.symm) he
  rwa [RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex_symm_apply, RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex_symm_apply] at hh

variable (e : I ≃ J) {S : Submodule ℂ ((I → K) → ℂ)} {T : Submodule ℂ ((J → K) → ℂ)}
  (E : S ≃ₗ[ℂ] T)
  (hE : ∀ f : S, ∀ y : J → K, (E f).val y = f.val (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm y))
  (hEi : ∀ f : T, ∀ x : I → K, (E.symm f).val x = f.val (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e x))
  {μI : Measure (I → K)} {μJ : Measure (J → K)}
  (hpair : ∀ f h : S, (∫ y, (E f).val y * star ((E h).val y) ∂μJ) =
    ∫ x, f.val x * star (h.val x) ∂μI)
  {Mp : Type*} [Group Mp] {ψ : AddChar K ℂ}
  (C : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover K ψ μJ T Mp)

def projection : Mp →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I K := (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e.symm).comp C.project

def action : Mp →* (S ≃ₗ[ℂ] S) := (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.conjugateLinearAut E.symm).comp C.action

omit [TopologicalSpace K] in
theorem projection_surjective : Function.Surjective (projection e C) := by
  intro g
  obtain ⟨m, hm⟩ := C.surjective (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e g)
  refine ⟨m, ?_⟩
  change RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e.symm (C.project m) = g
  rw [hm, RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex_symm_apply]

omit [TopologicalSpace K] in
theorem kernel (m : Mp) : projection e C m = 1 ↔ m = 1 ∨ m = C.negOne := by
  have he : projection e C m = 1 ↔ C.project m = 1 := by
    change RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e.symm (C.project m) = 1 ↔ _
    rw [← (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e.symm (K := K)).map_one]
    exact (symplectic_injective e.symm).eq_iff
  exact he.trans (C.kernel m)

omit [Fintype I] [DecidableEq I] [TopologicalSpace K] in
theorem genuine (f : S) : CM.action E C C.negOne f = -f := by
  change E.symm (C.action C.negOne (E f)) = -f
  rw [C.genuine, map_neg, LinearEquiv.symm_apply_apply]

omit [TopologicalSpace K] in
theorem faithful : Function.Injective (fun m => (projection e C m, CM.action E C m)) := by
  intro m l he
  apply C.faithful
  apply Prod.ext
  · exact symplectic_injective e.symm (congrArg Prod.fst he)
  · apply LinearEquiv.ext
    intro f
    have hh := congrArg (fun U : S ≃ₗ[ℂ] S => E (U (E.symm f))) (congrArg Prod.snd he)
    change E (E.symm (C.action m (E (E.symm f)))) = E (E.symm (C.action l (E (E.symm f)))) at hh
    simpa only [LinearEquiv.apply_symm_apply] using hh

include hpair in
omit [Fintype I] [DecidableEq I] [TopologicalSpace K] in
theorem unitary (m : Mp) (f h : S) :
    (∫ x, (CM.action E C m f).val x * star ((CM.action E C m h).val x) ∂μI) =
      ∫ x, f.val x * star (h.val x) ∂μI := by
  rw [← hpair, ← hpair f h]
  have hf : E (CM.action E C m f) = C.action m (E f) := E.apply_symm_apply _
  have hh : E (CM.action E C m h) = C.action m (E h) := E.apply_symm_apply _
  rw [hf, hh]
  exact C.unitary m (E f) (E h)

def cover : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover K ψ μI S Mp where
  project := projection e C
  action := CM.action E C
  surjective := projection_surjective e C
  negOne := C.negOne
  negOne_ne_one := C.negOne_ne_one
  project_negOne := by
    change RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e.symm (C.project C.negOne) = 1
    rw [C.project_negOne, map_one]
  kernel := CM.kernel e C
  genuine := CM.genuine E C
  faithful := CM.faithful e E C
  intertwines := fun m => Intertwiner.intertwines e S T E hE hEi ψ
    (C.project m) (C.action m) (C.intertwines m)
  unitary := CM.unitary E hpair C

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SchrodingerReindex.CM

end

end OAI

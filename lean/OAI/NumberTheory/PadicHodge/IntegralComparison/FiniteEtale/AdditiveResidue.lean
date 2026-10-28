import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.PresheafTraceElements
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FiberSectionTrace

/-! # Additive Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.AdditiveResidue

noncomputable section

/-! Finite étale residue detection after any additive construction.
Scalar action is kept as the image of the original coefficient map, so
restriction of scalars, degree shifts, and supported cohomology can be
used without replacing the original residue class. -/
open _root_.CategoryTheory
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.PresheafTraceElements
variable {C : Type v} [Category C]
  (Q B k : Type u) [CommRing Q] [CommRing B] [CommRing k]
  [Algebra Q B] [Algebra Q k] [Module.Free Q B] [Module.Finite Q B] [Algebra.Etale Q B]
  (P : C ⥤ ModuleCat.{u} Q)
  (F : (C ⥤ ModuleCat.{u} Q) ⥤ AddCommGrpCat.{w}) [F.Additive]

theorem scalar_sub (r s : Q) : PresheafTrace.scalar Q P (r-s) = PresheafTrace.scalar Q P r - PresheafTrace.scalar Q P s := by
  apply NatTrans.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change (r-s) • y = r • y - s • y
  exact sub_smul r s y

variable (ε : B →ₐ[Q] k) (lift : k → Q)
  (hlift : ∀ x, algebraMap Q k (lift x) = x)
  (y : F.obj P)
  (hy : ∀ r : Q, algebraMap Q k r = 0 → F.map (PresheafTrace.scalar Q P r) y = 0)
  (z : B)
  (hz : (1 ⊗ₜ[Q] z : k ⊗[Q] B) = FiberSectionTrace.component Q B k ε)

include hlift hy hz in
theorem trace_scalar (x : B) :
    F.map (PresheafTrace.scalar Q P (Algebra.trace Q B (z*x))) y =
      F.map (PresheafTrace.scalar Q P (lift (ε x))) y := by
  have hk : algebraMap Q k (Algebra.trace Q B (z*x) - lift (ε x)) = 0 := by
    rw [map_sub, FiberSectionTrace.trace_lift Q B k ε z hz x, hlift, sub_self]
  have h := hy _ hk
  rw [scalar_sub, F.map_sub] at h
  change F.map (PresheafTrace.scalar Q P (Algebra.trace Q B (z*x))) y -
    F.map (PresheafTrace.scalar Q P (lift (ε x))) y = 0 at h
  exact sub_eq_zero.mp h

include hlift hy hz in
theorem eq_inserted (a : F.obj (PresheafTrace.tensor Q B P))
    (ha : ∀ x : B, F.map (PresheafTrace.pairing Q B P x) a = F.map (PresheafTrace.scalar Q P (lift (ε x))) y) :
    a = F.map (PresheafTrace.insertion Q B P z) y := by
  apply PresheafTraceElements.equals_inserted_element Q B P F a y z
  intro x
  exact (ha x).trans (trace_scalar Q B k P F ε lift hlift y hy z hz x).symm

include hlift hy in
theorem exists_residue (hQ : Function.Surjective (algebraMap Q k))
    (a : F.obj (PresheafTrace.tensor Q B P))
    (ha : ∀ x : B, F.map (PresheafTrace.pairing Q B P x) a = F.map (PresheafTrace.scalar Q P (lift (ε x))) y) :
    ∃ z : B, (1 ⊗ₜ[Q] z : k ⊗[Q] B) = FiberSectionTrace.component Q B k ε ∧
      ε z = 1 ∧ a = F.map (PresheafTrace.insertion Q B P z) y := by
  obtain ⟨z, hz, hε, _⟩ := FiberSectionTrace.exists_lift Q B k ε hQ
  exact ⟨z, hz, hε, eq_inserted Q B k P F ε lift hlift y hy z hz a ha⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.AdditiveResidue

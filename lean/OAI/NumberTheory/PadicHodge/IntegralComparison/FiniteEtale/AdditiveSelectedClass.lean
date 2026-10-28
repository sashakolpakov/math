import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.AdditiveResidue

/-! # Additive Selected Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.AdditiveSelectedClass

noncomputable section

/-! The selected finite residue is fixed by its component and is
annihilated by functions vanishing at the selected section. -/
open _root_.CategoryTheory
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {C : Type v} [Category C]
  (Q B k : Type u) [CommRing Q] [CommRing B] [CommRing k]
  [Algebra Q B] [Algebra Q k] [Module.Free Q B] [Module.Finite Q B] [Algebra.Etale Q B]
  (P : C ⥤ ModuleCat.{u} Q)
  (F : (C ⥤ ModuleCat.{u} Q) ⥤ AddCommGrpCat.{w}) [F.Additive]
  (ε : B →ₐ[Q] k) (lift : k → Q) (hlift : ∀ x, algebraMap Q k (lift x) = x)
  (y : F.obj P)
  (hy : ∀ r : Q, algebraMap Q k r = 0 → F.map (PresheafTrace.scalar Q P r) y = 0)
  (z : B)
  (hz : (1 ⊗ₜ[Q] z : k ⊗[Q] B) = FiberSectionTrace.component Q B k ε)

include hlift hy hz in
theorem pairing_inserted (b x : B) :
    F.map (PresheafTrace.pairing Q B P x) (F.map (PresheafTrace.insertion Q B P (z*b)) y) =
      F.map (PresheafTrace.scalar Q P (lift (ε (b*x)))) y := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, PresheafTrace.insertion_pairing, mul_assoc]
  exact AdditiveResidue.trace_scalar Q B k P F ε lift hlift y hy z hz (b*x)

include hlift hy hz in
theorem insertion_same (b₁ b₂ : B) (hb : ε b₁ = ε b₂) :
    F.map (PresheafTrace.insertion Q B P (z*b₁)) y = F.map (PresheafTrace.insertion Q B P (z*b₂)) y := by
  apply PresheafTraceElements.jointly_injective Q B P F
  intro x
  rw [pairing_inserted Q B k P F ε lift hlift y hy z hz,
    pairing_inserted Q B k P F ε lift hlift y hy z hz,
    map_mul, map_mul, hb]

include hlift hy hz in
theorem fixed (he : ε z = 1) :
    F.map (PresheafTrace.insertion Q B P (z*z)) y = F.map (PresheafTrace.insertion Q B P z) y := by
  have h := insertion_same Q B k P F ε lift hlift y hy z hz z 1 (he.trans (map_one ε).symm)
  simpa only [mul_one] using h

omit [Module.Free Q B] [Module.Finite Q B] [Algebra.Etale Q B] in
private theorem insertion_zero : PresheafTrace.insertion Q B P (0 : B) = 0 := by
  apply NatTrans.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (0 : B) ⊗ₜ[Q] x = 0
  exact TensorProduct.zero_tmul _ _

include hlift hy hz in
theorem annihilated (b : B) (hb : ε b = 0) :
    F.map (PresheafTrace.insertion Q B P (z*b)) y = 0 := by
  have h := insertion_same Q B k P F ε lift hlift y hy z hz b 0 (hb.trans (map_zero ε).symm)
  rw [mul_zero, insertion_zero, F.map_zero] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.AdditiveSelectedClass

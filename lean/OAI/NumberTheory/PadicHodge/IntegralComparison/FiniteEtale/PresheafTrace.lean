import OAI.NumberTheory.PadicHodge.IntegralComparison.HomPresheafDualFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.LineTrace

/-! # Presheaf Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.PresheafTrace

noncomputable section

/-! Finite étale trace duality on a whole coefficient diagram. Its
paired evaluations detect equality after any additive construction. -/
open _root_.CategoryTheory
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C : Type v} [Category C] (R B : Type u) [CommRing R] [CommRing B]
  [Algebra R B] [Module.Free R B] [Module.Finite R B] [Algebra.Etale R B]
  (P : C ⥤ ModuleCat.{u} R)

def tensor : C ⥤ ModuleCat.{u} R where
  obj a := ModuleCat.of R (B ⊗[R] P.obj a)
  map f := ModuleCat.ofHom ((P.map f).hom.lTensor B)
  map_id a := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change x ⊗ₜ[R] (P.map (𝟙 a)).hom y = x ⊗ₜ[R] y
    rw [P.map_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change x ⊗ₜ[R] (P.map (f ≫ g)).hom y = x ⊗ₜ[R] (P.map g).hom ((P.map f).hom y)
    rw [P.map_comp]
    rfl

def duality : tensor R B P ≅ HomCoefficientFunctor.homPresheaf R P (ModuleCat.of R B) :=
  NatIso.ofComponents (fun a => (LineTrace.equiv R B (P.obj a)).toModuleIso)
    (by
      intro a b f
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x y
      apply LinearMap.ext
      intro z
      exact ((P.map f).hom.map_smul (Algebra.trace R B (x*z)) y).symm)

def insertion (z : B) : P ⟶ tensor R B P where
  app a := ModuleCat.ofHom (TensorProduct.mk R B (P.obj a) z)
  naturality a b f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

def pairing (x : B) : tensor R B P ⟶ P :=
  (duality R B P).hom ≫ HomPresheafDualFrame.evaluation R P (ModuleCat.of R B) x

def scalar (r : R) : P ⟶ P where
  app a := ModuleCat.ofHom (r • LinearMap.id)
  naturality a b f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact ((P.map f).hom.map_smul r y).symm

theorem insertion_pairing (z x : B) : insertion R B P z ≫ pairing R B P x =
    scalar R P (Algebra.trace R B (z*x)) := by
  apply NatTrans.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rfl

variable {D : Type*} [Category* D] [Preadditive D]
  (F : (C ⥤ ModuleCat.{u} R) ⥤ D) [F.Additive]

include F in
theorem jointly_monic {T : D} (a b : T ⟶ F.obj (tensor R B P))
    (h : ∀ x : B, a ≫ F.map (pairing R B P x) = b ≫ F.map (pairing R B P x)) : a = b := by
  obtain ⟨ι, hι, ⟨frame⟩⟩ := IntegralComparison.Finite.DualFrame.exists_frame R B
  let := hι
  have he : a ≫ F.map (duality R B P).hom = b ≫ F.map (duality R B P).hom := by
    apply HomPresheafDualFrame.jointly_monic R P (ModuleCat.of R B) frame F
    intro i
    simpa only [pairing, Category.assoc, ← F.map_comp] using h (frame.vector i)
  exact (cancel_mono (F.map (duality R B P).hom)).mp he

include F in
theorem equals_inserted {T : D} (a : T ⟶ F.obj (tensor R B P))
    (y : T ⟶ F.obj P) (z : B)
    (h : ∀ x : B, a ≫ F.map (pairing R B P x) =
      y ≫ F.map (scalar R P (Algebra.trace R B (z*x)))) :
    a = y ≫ F.map (insertion R B P z) := by
  apply jointly_monic R B P F
  intro x
  rw [Category.assoc, ← F.map_comp, insertion_pairing]
  exact h x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.PresheafTrace

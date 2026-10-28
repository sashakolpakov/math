import OAI.NumberTheory.PadicHodge.IntegralComparison.SequentialModuleDifference
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Sequential Kernel Limit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SequentialKernelLimit

noncomputable section

/-!
# IntegralComparison: the kernel of the countable difference is the native inverse limit
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable (R : Type u) [Ring R] (M : ℕ → Type v)
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  (t : ∀ n, M (n + 1) →ₗ[R] M n)

def diagram : ℕᵒᵖ ⥤ ModuleCat.{v} R :=
  Functor.ofOpSequence (X := fun n => ModuleCat.of R (M n)) (fun n => ModuleCat.ofHom (t n))

def cone : Cone (diagram R M t) where
  pt := ModuleCat.of R (LinearMap.ker (SequentialModuleDifference.difference R M t))
  π := NatTrans.ofOpSequence
    (fun n => ModuleCat.ofHom
      { toFun := fun x => x.val n
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }) (fun n => by
      simp only [Functor.const_obj_map, diagram, Functor.ofOpSequence_map_homOfLE_succ]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact ((SequentialModuleDifference.difference_eq_zero_iff R M t x.val).mp x.property n).symm)

def lift (s : Cone (diagram R M t)) : s.pt ⟶ (cone R M t).pt :=
  ModuleCat.ofHom
    { toFun := fun x => ⟨fun n => s.π.app (op n) x,
        (SequentialModuleDifference.difference_eq_zero_iff R M t _).mpr (fun n => by
          have h := s.w (homOfLE (Nat.le_succ n)).op
          change s.π.app (op (n + 1)) ≫ (diagram R M t).map (homOfLE (Nat.le_succ n)).op = s.π.app (op n) at h
          rw [show (diagram R M t).map (homOfLE (Nat.le_succ n)).op = ModuleCat.ofHom (t n) from
            Functor.ofOpSequence_map_homOfLE_succ _ n] at h
          exact congrArg (fun g : s.pt ⟶ ModuleCat.of R (M n) => g x) h)⟩
      map_add' := fun x y => Subtype.ext (funext (fun n => (s.π.app (op n)).hom.map_add x y))
      map_smul' := fun r x => Subtype.ext (funext (fun n => (s.π.app (op n)).hom.map_smul r x)) }

def isLimit : IsLimit (cone R M t) where
  lift := SequentialKernelLimit.lift R M t
  fac s n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  uniq s a ha := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext n
    exact congrArg (fun g : s.pt ⟶ ModuleCat.of R (M n) => g x) (ha (op n))

def limitIso : ModuleCat.of R (LinearMap.ker (SequentialModuleDifference.difference R M t)) ≅
    limit (diagram R M t) :=
  (SequentialKernelLimit.isLimit R M t).conePointUniqueUpToIso (limit.isLimit (diagram R M t))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SequentialKernelLimit

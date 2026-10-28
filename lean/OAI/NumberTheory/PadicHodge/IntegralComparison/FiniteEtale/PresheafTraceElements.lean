import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.PresheafTrace
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable

/-! # Presheaf Trace Elements -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.PresheafTraceElements

noncomputable section

/-! Elementwise finite-étale trace detection in the genuine additive
cohomology groups, without imposing linearity on the cohomology functor. -/
open _root_.CategoryTheory
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {C : Type v} [Category C] (R B : Type u) [CommRing R] [CommRing B]
  [Algebra R B] [Module.Free R B] [Module.Finite R B] [Algebra.Etale R B]
  (P : C ⥤ ModuleCat.{u} R)
  (F : (C ⥤ ModuleCat.{u} R) ⥤ AddCommGrpCat.{w}) [F.Additive]

theorem jointly_injective (a b : F.obj (PresheafTrace.tensor R B P))
    (h : ∀ x : B, F.map (PresheafTrace.pairing R B P x) a = F.map (PresheafTrace.pairing R B P x) b) : a = b := by
  let a₀ : AddCommGrpCat.of (ULift.{w} ℤ) ⟶ F.obj (PresheafTrace.tensor R B P) :=
    AddCommGrpCat.ofHom (uliftZMultiplesHom _ a)
  let b₀ : AddCommGrpCat.of (ULift.{w} ℤ) ⟶ F.obj (PresheafTrace.tensor R B P) :=
    AddCommGrpCat.ofHom (uliftZMultiplesHom _ b)
  have he : a₀ = b₀ := by
    apply PresheafTrace.jointly_monic R B P F
    intro x
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro n
    change F.map (PresheafTrace.pairing R B P x) (n.down • a) = F.map (PresheafTrace.pairing R B P x) (n.down • b)
    rw [map_zsmul, map_zsmul, h]
  have hn := ConcreteCategory.congr_hom he (ULift.up (1 : ℤ))
  change (1 : ℤ) • a = (1 : ℤ) • b at hn
  simpa only [one_zsmul] using hn

theorem equals_inserted_element (a : F.obj (PresheafTrace.tensor R B P)) (y : F.obj P) (z : B)
    (h : ∀ x : B, F.map (PresheafTrace.pairing R B P x) a =
      F.map (PresheafTrace.scalar R P (Algebra.trace R B (z*x))) y) :
    a = F.map (PresheafTrace.insertion R B P z) y := by
  apply jointly_injective R B P F
  intro x
  have hm := ConcreteCategory.congr_hom
    (congrArg F.map (PresheafTrace.insertion_pairing R B P z x)) y
  rw [F.map_comp] at hm
  exact (h x).trans hm.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.PresheafTraceElements

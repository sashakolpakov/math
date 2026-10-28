import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent

/-! # Translation Tests -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.TranslationTests

noncomputable section

/-! Every relation of a coordinate quotient is an actual translation by its represented kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

private theorem point_property_congr {C : Type*} [Category C] {E B T : C} (f : E ⟶ B) (q : T ⟶ B)
    (P : ∀ x y : T ⟶ E, x ≫ f = q → y ≫ f = q → Prop)
    (x y x' y' : T ⟶ E) (hx : x ≫ f = q) (hy : y ≫ f = q)
    (hx' : x' ≫ f = q) (hy' : y' ≫ f = q) (ex : x = x') (ey : y = y')
    (h : P x y hx hy) : P x' y' hx' hy' := by
  subst x'
  subst y'
  exact h

variable {S : Scheme.{u}} {A X Y : Over S} [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (g : X ⟶ Y) [IsMonHom g]

/-- Testing a relation property on full scheme-kernel translations suffices for every pair of lifts. -/
theorem of_translations
    (P : ∀ (T : Over S) (q : T ⟶ A ⊗ Y) (a b : T ⟶ A ⊗ X),
      a ≫ (𝟙 A ⊗ₘ g) = q → b ≫ (𝟙 A ⊗ₘ g) = q → Prop)
    (ht : ∀ (T : Over S) (l : T ⟶ Kernel.Scheme.kernelObject g) (z w : T ⟶ X) (x : T ⟶ A),
      (l ≫ Kernel.Scheme.kernelInclusion g) * z = w →
      ∀ (q : T ⟶ A ⊗ Y) (hz : lift x z ≫ (𝟙 A ⊗ₘ g) = q) (hw : lift x w ≫ (𝟙 A ⊗ₘ g) = q),
        P T q (lift x z) (lift x w) hz hw)
    {T : Over S} (q : T ⟶ A ⊗ Y) (a b : T ⟶ A ⊗ X)
    (ha : a ≫ (𝟙 A ⊗ₘ g) = q) (hb : b ≫ (𝟙 A ⊗ₘ g) = q) : P T q a b ha hb := by
  have hr := Vertical.KernelDescent.relation g a b (ha.trans hb.symm)
  let l := Kernel.Pair.pointDifference g (a ≫ snd A X) (b ≫ snd A X) hr.1
  have h : (l ≫ Kernel.Scheme.kernelInclusion g) * (a ≫ snd A X) = b ≫ snd A X :=
    (mul_comm _ _).trans (Kernel.Linearization.difference_translates g (a ≫ snd A X) (b ≫ snd A X) hr.1)
  have hea : lift (a ≫ fst A X) (a ≫ snd A X) = a := by cat_disch
  have heb : lift (a ≫ fst A X) (b ≫ snd A X) = b := by rw [hr.2]; cat_disch
  have hla : lift (a ≫ fst A X) (a ≫ snd A X) ≫ (𝟙 A ⊗ₘ g) = q :=
    (congrArg (fun v => v ≫ (𝟙 A ⊗ₘ g)) hea).trans ha
  have hlb : lift (a ≫ fst A X) (b ≫ snd A X) ≫ (𝟙 A ⊗ₘ g) = q :=
    (congrArg (fun v => v ≫ (𝟙 A ⊗ₘ g)) heb).trans hb
  exact point_property_congr (𝟙 A ⊗ₘ g) q (P T q) _ _ a b hla hlb ha hb hea heb
    (ht T l (a ≫ snd A X) (b ≫ snd A X) (a ≫ fst A X) h q hla hlb)

/-- Native morphism compatibility on kernel translations implies compatibility on all quotient relations. -/
theorem hom_compatible (D E : Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent (𝟙 A ⊗ₘ g).left) (e : D.module ≅ E.module)
    (ht : ∀ (T : Over S) (l : T ⟶ Kernel.Scheme.kernelObject g) (z w : T ⟶ X) (x : T ⟶ A),
      (l ≫ Kernel.Scheme.kernelInclusion g) * z = w →
      ∀ (q : T ⟶ A ⊗ Y) (hz : lift x z ≫ (𝟙 A ⊗ₘ g) = q) (hw : lift x w ≫ (𝟙 A ⊗ₘ g) = q),
        (Scheme.Modules.pullback (lift x z).left).map e.hom ≫
          E.hom q.left (lift x z).left (lift x w).left (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) =
        D.hom q.left (lift x z).left (lift x w).left (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) ≫
          (Scheme.Modules.pullback (lift x w).left).map e.hom)
    {T : Over S} (q : T ⟶ A ⊗ Y) (a b : T ⟶ A ⊗ X)
    (ha : a ≫ (𝟙 A ⊗ₘ g) = q) (hb : b ≫ (𝟙 A ⊗ₘ g) = q) :
    (Scheme.Modules.pullback a.left).map e.hom ≫
        E.hom q.left a.left b.left (congrArg Over.Hom.left ha) (congrArg Over.Hom.left hb) =
      D.hom q.left a.left b.left (congrArg Over.Hom.left ha) (congrArg Over.Hom.left hb) ≫
        (Scheme.Modules.pullback b.left).map e.hom :=
  of_translations g (fun _T q a b ha hb =>
    (Scheme.Modules.pullback a.left).map e.hom ≫
        E.hom q.left a.left b.left (congrArg Over.Hom.left ha) (congrArg Over.Hom.left hb) =
      D.hom q.left a.left b.left (congrArg Over.Hom.left ha) (congrArg Over.Hom.left hb) ≫
        (Scheme.Modules.pullback b.left).map e.hom) ht q a b ha hb

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.TranslationTests

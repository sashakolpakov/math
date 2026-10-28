import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Descent
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Function Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FunctionDescent

noncomputable section

/-! Regular functions descend through an effective quotient. This is
proved through the affine scheme adjunction, without module descent inputs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u
variable {X Y : Scheme.{u}}

theorem appTop_injective_of_epi (f : X ⟶ Y) [Epi f] :
    Function.Injective f.appTop := by
  let := ΓSpec.adjunction.isLeftAdjoint
  have : Epi (Scheme.Γ.rightOp.map f) := inferInstance
  have : Mono f.appTop := by
    have : Epi f.appTop.op := inferInstanceAs (Epi (Scheme.Γ.rightOp.map f))
    refine ⟨fun {Z} a b hab => ?_⟩
    apply Quiver.Hom.op_inj
    apply (cancel_epi f.appTop.op).mp
    exact congrArg Quiver.Hom.op hab
  exact ConcreteCategory.injective_of_mono_of_preservesPullback f.appTop

/-- A ring homomorphism into global functions descends when its associated
map to an affine scheme is constant on every quotient fiber. -/
theorem globalRingHom_desc (f : X ⟶ Y) [EffectiveEpi f]
    (R : CommRingCat.{u}) (a : R ⟶ Γ(X, ⊤))
    (ha : ∀ {T : Scheme.{u}} (p q : T ⟶ X), p ≫ f = q ≫ f →
      a ≫ p.appTop = a ≫ q.appTop) :
    ∃ b : R ⟶ Γ(Y, ⊤), b ≫ f.appTop = a := by
  let g : X ⟶ Spec R := (ΓSpec.adjunction.homEquiv X (.op R)) a.op
  have hg {T : Scheme.{u}} (p q : T ⟶ X) (hpq : p ≫ f = q ≫ f) : p ≫ g = q ≫ g := by
    calc
      _ = (ΓSpec.adjunction.homEquiv T (.op R)) (Scheme.Γ.rightOp.map p ≫ a.op) :=
        (ΓSpec.adjunction.homEquiv_naturality_left p a.op).symm
      _ = (ΓSpec.adjunction.homEquiv T (.op R)) (Scheme.Γ.rightOp.map q ≫ a.op) :=
        congrArg (ΓSpec.adjunction.homEquiv T (.op R))
          (congrArg Quiver.Hom.op (ha p q hpq))
      _ = _ := ΓSpec.adjunction.homEquiv_naturality_left q a.op
  let d : Y ⟶ Spec R := EffectiveEpi.desc f g hg
  let b : R ⟶ Γ(Y, ⊤) := ((ΓSpec.adjunction.homEquiv Y (.op R)).symm d).unop
  refine ⟨b, ?_⟩
  suffices h : (b ≫ f.appTop).op = a.op from congrArg Quiver.Hom.unop h
  apply (ΓSpec.adjunction.homEquiv X (.op R)).injective
  change (ΓSpec.adjunction.homEquiv X (.op R))
    (Scheme.Γ.rightOp.map f ≫ (ΓSpec.adjunction.homEquiv Y (.op R)).symm d) = g
  rw [ΓSpec.adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
  exact EffectiveEpi.fac f g hg

/-- A regular function invariant on every pair of test maps with the
same quotient image is the pullback of an actual regular function. -/
theorem globalSection_desc {X Y : Scheme.{0}} (f : X ⟶ Y) [EffectiveEpi f]
    (r : Γ(X, ⊤))
    (hr : ∀ {T : Scheme.{0}} (p q : T ⟶ X), p ≫ f = q ≫ f →
      p.appTop r = q.appTop r) :
    ∃ s : Γ(Y, ⊤), f.appTop s = r := by
  let R : CommRingCat := .of (Polynomial ℤ)
  let a : R ⟶ Γ(X, ⊤) := CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) r)
  have ha {T : Scheme.{0}} (p q : T ⟶ X) (hpq : p ≫ f = q ≫ f) :
      a ≫ p.appTop = a ≫ q.appTop := by
    apply CommRingCat.hom_ext
    change p.appTop.hom.comp (Polynomial.eval₂RingHom (Int.castRingHom _) r) =
      q.appTop.hom.comp (Polynomial.eval₂RingHom (Int.castRingHom _) r)
    ext <;> simp [hr p q hpq]
  obtain ⟨b, hb⟩ := globalRingHom_desc f R a ha
  refine ⟨b Polynomial.X, ?_⟩
  have h := ConcreteCategory.congr_hom hb Polynomial.X
  change f.appTop (b Polynomial.X) =
    Polynomial.eval₂ (Int.castRingHom _) r Polynomial.X at h
  simpa only [Polynomial.eval₂_X] using h

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FunctionDescent

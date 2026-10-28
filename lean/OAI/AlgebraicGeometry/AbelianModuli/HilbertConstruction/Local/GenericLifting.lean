import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PointClosureLocalTest
import OAI.RepresentationTheory.Theta.Geometric.SpecLocalRings

/-! # Generic Lifting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.GenericLifting

noncomputable section

/-! Integral local lifting is preserved by base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

def LocalGenericLifting {X Y : Scheme.{0}} (f : X ⟶ Y) : Prop :=
  ∀ (T : Scheme.{0}) [IsAffine T] [IsLocalRing Γ(T, ⊤)]
    [IsNoetherianRing Γ(T, ⊤)] [IsLocallyNoetherian T] [IsIntegral T]
    (a : T ⟶ Y) (x : X), a (genericPoint T) = f x →
      ∃ b : T ⟶ X, b ≫ f = a

theorem LocalGenericLifting.baseChange {X Y Y' : Scheme.{0}} {f : X ⟶ Y}
    (h : LocalGenericLifting f) (g : Y' ⟶ Y) :
    LocalGenericLifting (pullback.snd f g) := by
  intro T _ _ _ _ _ a x hx
  have hg : (a ≫ g) (genericPoint T) = f ((pullback.fst f g) x) := by
    calc
      (a ≫ g) (genericPoint T) = g ((pullback.snd f g) x) := congrArg g hx
      _ = f ((pullback.fst f g) x) :=
        congrArg (fun k : pullback f g ⟶ Y => k x) (pullback.condition (f := f) (g := g)).symm
  obtain ⟨b, hb⟩ := h T (a ≫ g) ((pullback.fst f g) x) hg
  exact ⟨pullback.lift b a hb, pullback.lift_snd b a hb⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.GenericLifting

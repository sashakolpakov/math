import OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalSchemeCocycle

/-! # Natural Scheme Cocycle -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.NaturalSchemeCocycle

noncomputable section

/-! Construct the actual regular cocycle of a commutative multiplicative line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineCocycle

variable {S : Scheme.{u}} {H : Over S} [GrpObj H]
  (L : Bundles.LineBundle H.left) (D : MultiplicativeLineData.MultiplicativeData L)
  (F : ∀ {T : Over S} (a : T ⟶ H), AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Fibers.fiber L a)

/-- The coefficient is independent of naming the same product by an equality. -/
theorem value_target {T : Over S} (a b c : T ⟶ H) (hab : a * b = c) :
    MultiplicativeLineCocycle.value L D F a b c hab = MultiplicativeLineCocycle.value L D F a b (a * b) rfl := by
  subst c
  rfl

variable [IsCommMonObj H]
  (hu : ∀ T : Over S, F (1 : T ⟶ H) = D.unitFrame)
  (hn : ∀ {T U : Over S} (g : U ⟶ T) (a : T ⟶ H) (a' : U ⟶ H) (ha : g ≫ a = a'),
    Fibers.pullSection L g a a' ha (F a).hom = (F a').hom)
  (hcomm : ∀ {T : Over S} (a b c : T ⟶ H) (hab : a * b = c) (hba : b * a = c)
    (U : T.left.Opens) (s : Γ(Fibers.fiber L a, U)) (t : Γ(Fibers.fiber L b, U)),
      (D.product a b c hab).app U s t = (D.product b a c hba).app U t s)

/-- All cocycle laws come from the actual line multiplication and the constructed frame family. -/
def cocycle : NaturalSchemeCocycle.NaturalCocycle H where
  value a b := MultiplicativeLineCocycle.value L D F a b (a * b) rfl
  natural g a b := by
    have hc : g ≫ (a * b) = (g ≫ a) * (g ≫ b) := MonObj.comp_mul g a b
    exact (NaturalProductFrames.coefficient_natural L D F g a b (a * b) rfl
      (g ≫ a) (g ≫ b) ((g ≫ a) * (g ≫ b)) rfl rfl rfl hc
      (hn g a (g ≫ a) rfl) (hn g b (g ≫ b) rfl) (hn g (a * b) _ hc)).symm
  one_left a :=
    (value_target L D F 1 a a (one_mul a)).symm.trans (MultiplicativeLineCocycle.value_one_left L D F a (hu _))
  one_right a :=
    (value_target L D F a 1 a (mul_one a)).symm.trans (MultiplicativeLineCocycle.value_one_right L D F a (hu _))
  symmetric a b :=
    (MultiplicativeLineCocycle.value_symmetric L D F a b (a * b) rfl (mul_comm b a) (hcomm a b (a * b) rfl (mul_comm b a))).trans
      (value_target L D F b a (a * b) (mul_comm b a))
  cocycle a b c := by
    have h := MultiplicativeLineCocycle.cocycle L D F a b c (a * b) (b * c) (a * (b * c))
      rfl rfl rfl (mul_assoc a b c)
    rw [value_target L D F (a * b) c (a * (b * c)) (mul_assoc a b c)] at h
    exact h.symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.NaturalSchemeCocycle

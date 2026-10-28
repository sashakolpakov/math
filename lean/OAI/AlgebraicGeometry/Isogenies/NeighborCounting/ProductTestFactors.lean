import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

/-! # Product Test Factors -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProductTestFactors

noncomputable section

/-! An arbitrary test map into a product family factors through a graph
and a map of product families. Equal image maps use the same graph. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S : Scheme.{u}} (P : Over S) {T B V : Over S}

theorem graph_factor (e : V ⟶ T ⊗ P) :
    lift (𝟙 V) (e ≫ snd T P) ≫ ((e ≫ fst T P) ▷ P) = e := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, whiskerRight_fst, lift_fst_assoc, Category.id_comp]
  · simp only [Category.assoc, whiskerRight_snd, lift_snd]

variable {Z : Scheme.{u}}

def testObject (p : Z ⟶ (B ⊗ P).left) : Over S := Over.mk (p ≫ (B ⊗ P).hom)

def targetLift (p : Z ⟶ (B ⊗ P).left) : testObject P p ⟶ B ⊗ P := Over.homMk p rfl

def testLift (t : T ⟶ B) (p : Z ⟶ (B ⊗ P).left) (x : Z ⟶ (T ⊗ P).left)
    (hx : x ≫ (t ▷ P).left = p) : testObject P p ⟶ T ⊗ P :=
  Over.homMk x (by
    change x ≫ (T ⊗ P).hom = p ≫ (B ⊗ P).hom
    rw [← Over.w (t ▷ P), ← Category.assoc, hx])

theorem testLift_comp (t : T ⟶ B) (p : Z ⟶ (B ⊗ P).left) (x : Z ⟶ (T ⊗ P).left)
    (hx : x ≫ (t ▷ P).left = p) : testLift P t p x hx ≫ (t ▷ P) = targetLift P p := by
  apply Over.OverMorphism.ext
  exact hx

def baseMap (t : T ⟶ B) (p : Z ⟶ (B ⊗ P).left) (x : Z ⟶ (T ⊗ P).left)
    (hx : x ≫ (t ▷ P).left = p) : testObject P p ⟶ T :=
  testLift P t p x hx ≫ fst T P

def baseTarget (p : Z ⟶ (B ⊗ P).left) : testObject P p ⟶ B := targetLift P p ≫ fst B P

def graph (p : Z ⟶ (B ⊗ P).left) : testObject P p ⟶ testObject P p ⊗ P :=
  lift (𝟙 _) (targetLift P p ≫ snd B P)

theorem baseMap_comp (t : T ⟶ B) (p : Z ⟶ (B ⊗ P).left) (x : Z ⟶ (T ⊗ P).left)
    (hx : x ≫ (t ▷ P).left = p) : baseMap P t p x hx ≫ t = baseTarget P p := by
  unfold baseMap baseTarget
  rw [Category.assoc, ← whiskerRight_fst, ← Category.assoc, testLift_comp]

theorem testLift_snd (t : T ⟶ B) (p : Z ⟶ (B ⊗ P).left) (x : Z ⟶ (T ⊗ P).left)
    (hx : x ≫ (t ▷ P).left = p) :
    testLift P t p x hx ≫ snd T P = targetLift P p ≫ snd B P := by
  rw [← whiskerRight_snd t P, ← Category.assoc, testLift_comp]

theorem graph_to_test (t : T ⟶ B) (p : Z ⟶ (B ⊗ P).left) (x : Z ⟶ (T ⊗ P).left)
    (hx : x ≫ (t ▷ P).left = p) :
    (graph P p).left ≫ (baseMap P t p x hx ▷ P).left = x := by
  have h := graph_factor P (testLift P t p x hx)
  rw [testLift_snd] at h
  exact congrArg Over.Hom.left h

theorem graph_to_target (p : Z ⟶ (B ⊗ P).left) :
    (graph P p).left ≫ (baseTarget P p ▷ P).left = p :=
  congrArg Over.Hom.left (graph_factor P (targetLift P p))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProductTestFactors

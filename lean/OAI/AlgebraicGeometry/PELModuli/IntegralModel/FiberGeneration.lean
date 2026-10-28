import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Words

/-! # Fiber Generation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-!
The specialization theorem applied to the actual finite-difference morphism.
Geometric points are related to points of a pullback by an explicit equivalence.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

/-- A point of the fiber is exactly a point of the original scheme over the
specified base point. Both maps are constructed using the scheme pullback. -/
def FiberGeneration.fiberPointsEquiv {B : Scheme.{u}} (X : Over B)
    {Ω : Type u} [Field Ω] (t : Spec (.of Ω) ⟶ B) :
    (Over.mk (𝟙 (Spec (.of Ω))) ⟶ (Over.pullback t).obj X) ≃
      (Over.mk t ⟶ X) where
  toFun p := Over.homMk (p.left ≫ pullback.fst X.hom t) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hp : p.left ≫ pullback.snd X.hom t = 𝟙 _ := p.w
    rw [hp]
    exact Category.id_comp t)
  invFun p := Over.homMk (pullback.lift p.left (𝟙 _)
    (p.w.trans (Category.id_comp t).symm)) (pullback.lift_snd _ _ _)
  left_inv p := by
    ext1
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans p.w.symm
  right_inv p := by ext1; exact pullback.lift_fst _ _ _

@[reassoc]
theorem FiberGeneration.fiberPointsEquiv_naturality {B : Scheme.{u}} {X Y : Over B}
    (f : X ⟶ Y) {Ω : Type u} [Field Ω] (t : Spec (.of Ω) ⟶ B)
    (p : Over.mk (𝟙 (Spec (.of Ω))) ⟶ (Over.pullback t).obj X) :
    FiberGeneration.fiberPointsEquiv Y t (p ≫ (Over.pullback t).map f) =
      FiberGeneration.fiberPointsEquiv X t p ≫ f := by
  ext1
  change (p.left ≫ pullback.lift _ _ _) ≫ pullback.fst Y.hom t =
    (p.left ≫ pullback.fst X.hom t) ≫ f.left
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc]

/-- Generic surjectivity supplies points over every algebraically closed
field at every base point, expressed in the original slice category. -/
theorem FiberGeneration.points_surjective_of_dominant_base_change
    {B T : Scheme.{u}} (g : T ⟶ B) [IsDominant g]
    {X Y : Over B} (f : X ⟶ Y)
    [IsProper f.left] [UniversallyOpen Y.hom]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (hgeneric : Surjective ((Over.pullback g).map f).left)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ B) :
    Function.Surjective (fun p : Over.mk t ⟶ X => p ≫ f) := by
  intro y
  obtain ⟨p, hp⟩ := Specialization.every_geometric_fiber_point_surjective g f hgeneric Ω t
    ((FiberGeneration.fiberPointsEquiv Y t).symm y)
  change p ≫ (Over.pullback t).map f = (FiberGeneration.fiberPointsEquiv Y t).symm y at hp
  refine ⟨FiberGeneration.fiberPointsEquiv X t p, ?_⟩
  dsimp only
  rw [← FiberGeneration.fiberPointsEquiv_naturality, hp, Equiv.apply_symm_apply]

/-- The same finite number of differences works on every geometric fiber.
All properness and base-change compatibility come from the constructed word
morphism; no special-fiber generation assertion is assumed. -/
theorem FiberGeneration.difference_sums_surjective_on_geometric_fibers
    {B T : Scheme.{u}} (g : T ⟶ B) [IsDominant g]
    {X A : Over B} [GrpObj A] [IsCommMonObj A]
    [IsProper X.hom] [IsProper A.hom] [Smooth A.hom]
    (a : X ⟶ A) (n : ℕ)
    (hgeneric : Surjective ((Over.pullback g).map (Words.DifferenceWords.map a n)).left)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ B) :
    Function.Surjective
      (fun z : Fin n → (Over.mk t ⟶ X) × (Over.mk t ⟶ X) =>
        ∑ i, (Additive.ofMul ((z i).1 ≫ a) - Additive.ofMul ((z i).2 ≫ a))) := by
  apply (Words.DifferenceWords.sum_surjective_iff a (Over.mk t) n).mpr
  exact FiberGeneration.points_surjective_of_dominant_base_change g (Words.DifferenceWords.map a n)
    hgeneric Ω t

theorem Components.ComponentAlbaneseData.sumOfDifferences_surjective
    {B T : Scheme} (g : T ⟶ B) [IsDominant g]
    {M : Over B} {r : ℕ} (D : Components.ComponentAlbaneseData M r) (j : Fin r)
    [IsProper (D.S j).hom] [IsProper (D.A j).X.hom] [Smooth (D.A j).X.hom]
    (n : ℕ)
    (hgeneric : Surjective ((Over.pullback g).map
      (Words.DifferenceWords.map (D.a j) n)).left) (t : Base.GeometricPoint B) :
    Function.Surjective (D.sumOfDifferences j n t) :=
  FiberGeneration.difference_sums_surjective_on_geometric_fibers g (D.a j) n hgeneric t.field t.morphism

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel

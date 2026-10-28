import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Open
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Group.Abelian

/-! # Models Has -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ModelsHas

noncomputable section

/-!
The SpreadingOut finite-diagram proposition is exposed as an explicit hypothesis.
`FiniteDiagram` packages precisely its input data and hypotheses;
`DiagramModel` packages precisely its existing existential conclusion.
Neither bundle includes surjectivity or Albanese generation. The theorem
at the end proves that every originally surjective arrow remains surjective.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- SpreadingOut's finite disjoint open decomposition with connected geometric fibers. -/
def HasSplitGeometricComponents {S : Scheme.{u}} (X : Over S) : Prop :=
  ∃ (n : ℕ) (C : Fin n → X.left.Opens),
    (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
    (⨆ i, C i) = ⊤ ∧
    ∀ i, GeometricallyConnected ((C i).ι ≫ X.hom)

/-- The input data and hypotheses in SpreadingOut's simultaneous spreading theorem. -/
structure FiniteDiagram (K : Type u) [Field K] [NumberField K] where
  objects : Type u
  arrows : Type u
  abelians : Type u
  [finiteObjects : Fintype objects]
  [finiteArrows : Fintype arrows]
  [finiteAbelians : Fintype abelians]
  X : objects → Over (Arithmetic.Open.fieldBase K)
  smooth : ∀ i, Smooth (X i).hom
  proper : ∀ i, IsProper (X i).hom
  src : arrows → objects
  dst : arrows → objects
  f : ∀ a, X (src a) ⟶ X (dst a)
  abelianIndex : abelians → objects
  group : ∀ b, GrpObj (X (abelianIndex b))
  abelian : ∀ b,
    letI := group b
    IsCommMonObj (X (abelianIndex b)) ∧
      GeometricallyConnected (X (abelianIndex b)).hom

attribute [instance] FiniteDiagram.finiteObjects FiniteDiagram.finiteArrows
  FiniteDiagram.finiteAbelians

/-- Exactly the model data and properties already supplied by SpreadingOut. -/
structure DiagramModel {K : Type u} [Field K] [NumberField K]
    (D : FiniteDiagram K) where
  extension : Arithmetic.Open.FiniteNumberFieldExtension K
  base : Arithmetic.Open.ArithmeticOpen extension.carrier
  M : D.objects → Over base.U.toScheme
  fM : ∀ a, M (D.src a) ⟶ M (D.dst a)
  e : ∀ i, (Over.pullback base.generic).obj (M i) ≅
    (Over.pullback (Spec.map
      (CommRingCat.ofHom (algebraMap K extension.carrier)))).obj (D.X i)
  groupM : ∀ b, GrpObj (M (D.abelianIndex b))
  properties : ∀ i,
    Smooth (M i).hom ∧ IsProper (M i).hom ∧
      HasSplitGeometricComponents (M i)
  compatible : ∀ a,
    (Over.pullback base.generic).map (fM a) ≫ (e (D.dst a)).hom =
      (e (D.src a)).hom ≫ (Over.pullback (Spec.map
        (CommRingCat.ofHom (algebraMap K extension.carrier)))).map (D.f a)
  abelian : ∀ b,
    letI := D.group b
    letI := groupM b
    letI : GrpObj
        ((Over.pullback base.generic).obj (M (D.abelianIndex b))) :=
      Functor.grpObjObj (F := Over.pullback base.generic)
    letI : GrpObj ((Over.pullback (Spec.map
        (CommRingCat.ofHom (algebraMap K extension.carrier)))).obj
          (D.X (D.abelianIndex b))) :=
      Functor.grpObjObj (F := Over.pullback (Spec.map
        (CommRingCat.ofHom (algebraMap K extension.carrier))))
    IsCommMonObj (M (D.abelianIndex b)) ∧
      GeometricallyConnected (M (D.abelianIndex b)).hom ∧
      IsMonHom (e (D.abelianIndex b)).hom

/-- SpreadingOut's supplied proposition, without using the admitted theorem stub. -/
def SpreadingOutInput (K : Type u) [Field K] [NumberField K] : Prop :=
  ∀ D : FiniteDiagram K, Nonempty (DiagramModel D)

/-- Every SpreadingOut model preserves surjectivity of every originally surjective
arrow. Thus no extra surjectivity hypothesis is imposed on the model. -/
theorem DiagramModel.preserves_surjectivity
    {K : Type u} [Field K] [NumberField K]
    {D : FiniteDiagram K} (M : DiagramModel D)
    (a : D.arrows) (ha : Surjective (D.f a).left) :
    Surjective (M.fM a).left := by
  let : Surjective (D.f a).left := ha
  let : IsProper (M.M (D.src a)).hom := (M.properties _).2.1
  let : IsProper (M.M (D.dst a)).hom := (M.properties _).2.1
  let : Smooth (M.M (D.dst a)).hom := (M.properties _).1
  exact Arithmetic.Open.model_map_surjective M.extension M.base (D.f a) (M.fM a)
    (M.e (D.src a)) (M.e (D.dst a)) (M.compatible a)

/-- Conditional on the precise SpreadingOut input, a simultaneous good model can
be chosen with all original surjective arrows still surjective. -/
theorem spread_surjective_diagram
    {K : Type u} [Field K] [NumberField K]
    (hSpreadingOut : SpreadingOutInput K) (D : FiniteDiagram K) :
    ∃ M : DiagramModel D,
      ∀ a : D.arrows, Surjective (D.f a).left → Surjective (M.fM a).left := by
  obtain ⟨M⟩ := hSpreadingOut D
  exact ⟨M, M.preserves_surjectivity⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ModelsHas

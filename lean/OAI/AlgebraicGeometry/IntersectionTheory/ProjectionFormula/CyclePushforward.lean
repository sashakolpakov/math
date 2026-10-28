import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Cycle Pushforward -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

noncomputable section

/-!
# ProjectionFormula: proper cycle pushforward in generic-point coordinates

The weights in the constructed pushforward are degrees of the actual residue
field extensions. Their tower law makes ungraded pushforward functorial. The
comparison with the graded cycle construction keeps all multiplicities.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

theorem residueDegree_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueDegree x = g.residueDegree (f x) * f.residueDegree x := by
  let K := Z.residueField (g (f x))
  let L := Y.residueField (f x)
  let M := X.residueField x
  let a : K →+* L := (g.residueFieldMap (f x)).hom
  let b : L →+* M := (f.residueFieldMap x).hom
  let : Algebra K L := a.toAlgebra
  let : Algebra L M := b.toAlgebra
  let : Algebra K M := ((f ≫ g).residueFieldMap x).hom.toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f g x))
  exact (Module.finrank_mul_finrank K L M).symm

/-- Finite cycle pushforward in native generic-point coordinates. -/
def pointPushforward {X Y : Scheme} (f : X ⟶ Y) : (X →₀ ℚ) →ₗ[ℚ] (Y →₀ ℚ) :=
  Finsupp.linearCombination ℚ
    (fun x => Finsupp.single (f x) (f.residueDegree x : ℚ))

theorem pointPushforward_single {X Y : Scheme} (f : X ⟶ Y) (x : X) (a : ℚ) :
    pointPushforward f (Finsupp.single x a) =
      Finsupp.single (f x) (a * (f.residueDegree x : ℚ)) := by
  rw [pointPushforward, Finsupp.linearCombination_single, Finsupp.smul_single]
  rfl

theorem pointPushforward_id (X : Scheme) : pointPushforward (𝟙 X) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro x a
  rw [pointPushforward_single, Scheme.Hom.residueDegree_id]
  simp only [Nat.cast_one, mul_one, LinearMap.id_apply]
  rfl

theorem pointPushforward_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pointPushforward (f ≫ g) = (pointPushforward g).comp (pointPushforward f) := by
  apply Finsupp.lhom_ext
  intro x a
  rw [LinearMap.comp_apply, pointPushforward_single, pointPushforward_single,
    pointPushforward_single, residueDegree_comp, Nat.cast_mul]
  congr 1
  ring

/-- The actual codimension-graded cycle placed at its generic points. -/
def pointCycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    X.RationalDimensionCycle p →ₗ[ℚ] (X.carrier →₀ ℚ) :=
  Finsupp.linearCombination ℚ
    (fun A => Finsupp.single (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) (1 : ℚ))

/-- Extraction of a homogeneous codimension component from a point cycle. -/
def degreeComponent (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    (X.carrier →₀ ℚ) →ₗ[ℚ] X.RationalDimensionCycle p :=
  Finsupp.linearCombination ℚ
    (fun x => CycleClass.Thom.IntersectionGeometry.supportInDegree X p (irreducibleSetEquivPoints.symm x))

theorem pointCycle_single (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (A : X.DimensionCycleSupport p) (a : ℚ) :
    pointCycle X p (Finsupp.single A a) = Finsupp.single (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) a := by
  rw [pointCycle, Finsupp.linearCombination_single]
  exact Finsupp.smul_single_one _ _

theorem degreeComponent_pointCycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    (degreeComponent X p).comp (pointCycle X p) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro A a
  rw [LinearMap.comp_apply, pointCycle_single, degreeComponent,
    Finsupp.linearCombination_single]
  have hA : irreducibleSetEquivPoints.symm (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = A.val :=
    irreducibleSetEquivPoints.symm_apply_apply A.val
  rw [hA]
  simp only [CycleClass.Thom.IntersectionGeometry.supportInDegree, dite_eq_left A.property]
  exact Finsupp.smul_single_one A a

/-- The ProjectionFormula graded operation is literally the requested component of ordinary
proper pushforward, not a different map on the same groups. -/
theorem cyclePushforward_eq_pointPushforward {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ) :
    ProperCycleLinearity.cyclePushforward f p q =
      (degreeComponent Y q).comp
        ((pointPushforward (show X.carrier ⟶ Y.carrier from f.left)).comp (pointCycle X p)) := by
  apply Finsupp.lhom_ext
  intro A a
  rw [LinearMap.comp_apply, LinearMap.comp_apply, pointCycle_single,
    pointPushforward_single, degreeComponent, Finsupp.linearCombination_single,
    ProperCycleLinearity.cyclePushforward_single]
  change a • ((f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) : ℚ) •
    CycleClass.Thom.IntersectionGeometry.supportInDegree Y q (ProperCycleLinearity.imageSupport f A.val)) = _
  rw [smul_smul]
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

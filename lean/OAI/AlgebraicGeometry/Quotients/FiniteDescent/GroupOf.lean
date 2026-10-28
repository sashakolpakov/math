import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Proper
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeFiniteness
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Group Of -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupOf

/-!
# Separatedness of a finite group-scheme quotient

The group diagonal is a base change of its identity section. For a finite
homomorphic image of a separated group scheme, that section is finite and
monomorphic, hence a closed immersion.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u v

namespace Construction.GroupGeometry

/-- The diagonal of a group is the fiber of the difference map over the
identity section. -/
theorem diagonal_isPullback
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] (G : C) [GrpObj G] :
    IsPullback (lift (𝟙 G) (𝟙 G)) (toUnit G)
      (fst G G * (snd G G)⁻¹) MonObj.one := by
  refine ⟨?_, ⟨PullbackCone.IsLimit.mk _ (fun c => c.fst ≫ fst G G) ?_ ?_ ?_⟩⟩
  · simp [MonObj.comp_mul, GrpObj.comp_inv, Hom.one_def]
  · intro c
    have he : (c.fst ≫ fst G G) * (c.fst ≫ snd G G)⁻¹ = 1 := by
      simpa only [MonObj.comp_mul, GrpObj.comp_inv,
        show c.snd = toUnit _ from toUnit_unique _ _, ← Hom.one_def] using c.condition
    apply hom_ext
    · simp
    · simpa using mul_inv_eq_one.mp he
  · intro c
    exact toUnit_unique _ _
  · intro c m hm _
    simpa using congrArg (fun f => f ≫ fst G G) hm

/-- A group scheme is separated if its identity section is a closed
immersion. -/
theorem separated_of_closed_identity {S : Scheme.{u}} (G : Over S) [GrpObj G]
    [IsClosedImmersion (MonObj.one (X := G)).left] : IsSeparated G.hom := by
  have h := (diagonal_isPullback G).map (Over.forget S)
  have : IsClosedImmersion (lift (𝟙 G) (𝟙 G)).left :=
    MorphismProperty.of_isPullback h.flip
      (inferInstanceAs (IsClosedImmersion (MonObj.one (X := G)).left))
  constructor
  exact this

/-- A finite homomorphic image of a separated group scheme is separated. -/
theorem separated_of_finite_quotient {S : Scheme.{u}} {A B : Over S}
    [GrpObj A] [GrpObj B] [IsSeparated A.hom]
    (q : A ⟶ B) [IsMonHom q] [IsFinite q.left] : IsSeparated B.hom := by
  have : IsClosedImmersion ((MonObj.one (X := A)).left ≫ A.hom) := by
    rw [(MonObj.one (X := A)).w]
    change IsClosedImmersion (𝟙 S)
    infer_instance
  have : IsClosedImmersion (MonObj.one (X := A)).left :=
    IsClosedImmersion.of_comp _ A.hom
  have : IsFinite (MonObj.one (X := B)).left := by
    rw [← IsMonHom.one_hom q]
    change IsFinite ((MonObj.one (X := A)).left ≫ q.left)
    infer_instance
  have : Mono (MonObj.one (X := B)).left := by
    have : Mono (𝟙 S) := inferInstance
    exact mono_of_mono_fac (show (MonObj.one (X := B)).left ≫ B.hom = 𝟙 S from
      (MonObj.one (X := B)).w)
  have : IsClosedImmersion (MonObj.one (X := B)).left :=
    (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩
  exact separated_of_closed_identity B

/-- Properness descends to a finite locally free group-scheme quotient of a
proper group scheme locally of finite presentation. -/
theorem proper_of_finite_quotient {S : Scheme.{u}} {A B : Over S}
    [GrpObj A] [GrpObj B] [IsProper A.hom] [LocallyOfFinitePresentation A.hom]
    (q : A ⟶ B) [IsMonHom q] [IsFinite q.left] [Flat q.left] [Surjective q.left]
    [LocallyOfFinitePresentation q.left] : IsProper B.hom := by
  have : IsSeparated B.hom := separated_of_finite_quotient q
  have : LocallyOfFinitePresentation (q.left ≫ B.hom) := by rw [q.w]; infer_instance
  have : LocallyOfFinitePresentation B.hom :=
    SchemeFiniteness.Construction.SchemeFinitenessDescent.locallyOfFinitePresentation q.left B.hom
  have : IsProper (q.left ≫ B.hom) := by rw [q.w]; infer_instance
  exact Proper.Construction.Geometry.proper_of_comp q.left B.hom

end Construction.GroupGeometry

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupOf

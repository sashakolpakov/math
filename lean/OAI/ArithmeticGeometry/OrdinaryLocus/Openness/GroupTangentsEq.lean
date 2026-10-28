import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TangentOperations
import Mathlib.AlgebraicGeometry.Group.Abelian

/-! # Group Tangents Eq -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupTangentsEq.Construction.GroupTangents

/-!
# Openness: infinitesimal points of group schemes

The identity section supplies the base point for the intrinsic lift module.
Relative infinitesimal points are the kernel of the map to base lifts.
All morphisms here are the actual morphisms of the group scheme.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

instance one_isMonHom {S : Scheme.{u}} (A B : Over S) [MonObj A] [MonObj B] :
    IsMonHom (1 : A ⟶ B) := by
  change IsMonHom (toUnit A ≫ η[B])
  infer_instance

variable {S : Scheme.{u}} {C : CommRingCat.{u}} [IsLocalRing C]
variable (s : Spec C ⟶ S) (J : Ideal C) (hJ : J ^ 2 = ⊥)

noncomputable def unitPoint (A : Over S) [MonObj A] : Under (Spec C) :=
  Under.mk ((1 : Over.mk s ⟶ A).left)

noncomputable def unitMap {A B : Over S} [MonObj A] [MonObj B]
    (f : A ⟶ B) [IsMonHom f] : unitPoint s A ⟶ unitPoint s B :=
  Under.homMk f.left (congrArg (fun z : Over.mk s ⟶ B => z.left) (MonObj.one_comp f))

omit [IsLocalRing C] in
theorem unitMap_comp_eq_id {A B : Over S} [MonObj A] [MonObj B]
    (f : A ⟶ B) (g : B ⟶ A) [IsMonHom f] [IsMonHom g] (h : f ≫ g = 𝟙 A) :
    unitMap s f ≫ unitMap s g = 𝟙 (unitPoint s A) := by
  apply Under.UnderMorphism.ext
  exact congrArg (fun z : A ⟶ A => z.left) h

omit [IsLocalRing C] in
theorem unitMap_comp_eq {A B D E : Over S} [MonObj A] [MonObj B] [MonObj D] [MonObj E]
    (f : A ⟶ B) (g : B ⟶ D) (f' : A ⟶ E) (g' : E ⟶ D)
    [IsMonHom f] [IsMonHom g] [IsMonHom f'] [IsMonHom g'] (h : f ≫ g = f' ≫ g') :
    unitMap s f ≫ unitMap s g = unitMap s f' ≫ unitMap s g' := by
  apply Under.UnderMorphism.ext
  exact congrArg (fun z : A ⟶ D => z.left) h

abbrev Space (A : Over S) [MonObj A] := PointedTangentAt.Construction.PointedTangent.Space J hJ (unitPoint s A).hom

noncomputable def point (A : Over S) [MonObj A] (v : Space s J hJ A) : Spec C ⟶ A.left :=
  PointedTangentAt.Construction.PointedTangent.point J hJ (unitPoint s A).hom v

@[simp] theorem point_zero (A : Over S) [MonObj A] :
    point s J hJ A 0 = (1 : Over.mk s ⟶ A).left :=
  PointedTangentAt.Construction.PointedTangent.point_zero J hJ (unitPoint s A).hom

theorem point_injective (A : Over S) [MonObj A] : Function.Injective (point s J hJ A) :=
  PointedTangentAt.Construction.PointedTangent.point_injective J hJ (unitPoint s A).hom

noncomputable def tangent {A B : Over S} [MonObj A] [MonObj B]
    (f : A ⟶ B) [IsMonHom f] : Space s J hJ A →ₗ[C] Space s J hJ B :=
  PointedTangentAt.Construction.PointedTangent.map J hJ (unitMap s f)

theorem point_tangent {A B : Over S} [MonObj A] [MonObj B]
    (f : A ⟶ B) [IsMonHom f] (v : Space s J hJ A) :
    point s J hJ B (tangent s J hJ f v) = point s J hJ A v ≫ f.left :=
  PointedTangentAt.Construction.PointedTangent.point_map J hJ (unitMap s f) v

theorem tangent_id (A : Over S) [MonObj A] :
    tangent s J hJ (𝟙 A) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply point_injective s J hJ A
  rw [point_tangent]
  rfl

theorem tangent_comp {A B D : Over S} [MonObj A] [MonObj B] [MonObj D]
    (f : A ⟶ B) (g : B ⟶ D) [IsMonHom f] [IsMonHom g] :
    tangent s J hJ (f ≫ g) = (tangent s J hJ g).comp (tangent s J hJ f) := by
  apply LinearMap.ext
  intro v
  apply point_injective s J hJ D
  change point s J hJ D (tangent s J hJ (f ≫ g) v) =
    point s J hJ D (tangent s J hJ g (tangent s J hJ f v))
  rw [point_tangent, point_tangent, point_tangent, Over.comp_left, Category.assoc]

/-- The actual base map on infinitesimal points. -/
noncomputable def relative (A : Over S) [MonObj A] : Submodule C (Space s J hJ A) :=
  LinearMap.ker (tangent s J hJ (toUnit A))

theorem point_over (A : Over S) [MonObj A] (v : relative s J hJ A) :
    point s J hJ A v.val ≫ A.hom = s := by
  have hv : tangent s J hJ (toUnit A) v.val = 0 := v.property
  have hp := point_tangent s J hJ (toUnit A) v.val
  rw [hv, point_zero] at hp
  exact hp.symm

/-- A relative tangent is realized as an actual point over the fixed base. -/
noncomputable def overPoint (A : Over S) [MonObj A] (v : relative s J hJ A) : Over.mk s ⟶ A :=
  Over.homMk (point s J hJ A v.val) (point_over s J hJ A v)

theorem overPoint_injective (A : Over S) [MonObj A] :
    Function.Injective (overPoint s J hJ A) := by
  intro v w h
  apply Subtype.ext
  apply point_injective s J hJ A
  exact congrArg (fun z : Over.mk s ⟶ A => z.left) h

@[simp] theorem overPoint_zero (A : Over S) [MonObj A] : overPoint s J hJ A 0 = 1 := by
  apply Over.OverMorphism.ext
  exact point_zero s J hJ A

theorem tangent_one {A B : Over S} [MonObj A] [MonObj B]
    (v : relative s J hJ A) : tangent s J hJ (1 : A ⟶ B) v.val = 0 := by
  change tangent s J hJ (toUnit A ≫ η[B]) v.val = 0
  rw [tangent_comp, LinearMap.comp_apply]
  have hv : tangent s J hJ (toUnit A) v.val = 0 := v.property
  rw [hv, map_zero]

/-- The module addition is the actual group multiplication on infinitesimal
points. The proof uses the two unit insertions and the scheme fiber product. -/
theorem overPoint_add (A : Over S) [MonObj A] [IsCommMonObj A]
    (v w : relative s J hJ A) :
    overPoint s J hJ A (v + w) = overPoint s J hJ A v * overPoint s J hJ A w := by
  let i₁ : A ⟶ A ⊗ A := lift (𝟙 A) (1 : A ⟶ A)
  let i₂ : A ⟶ A ⊗ A := lift (1 : A ⟶ A) (𝟙 A)
  obtain ⟨z, hp, hq, hm⟩ := TangentOperations.Construction.PointedTangent.exists_product_point J hJ
    (unitMap s (toUnit A)) (unitMap s η[A])
    (unitMap s (fst A A)) (unitMap s (snd A A)) (unitMap s μ[A])
    (unitMap s i₁) (unitMap s i₂)
    (unitMap_comp_eq_id s i₁ (fst A A) (lift_fst _ _))
    (unitMap_comp_eq s i₁ (snd A A) (toUnit A) η[A] (lift_snd _ _))
    (unitMap_comp_eq s i₂ (fst A A) (toUnit A) η[A] (lift_fst _ _))
    (unitMap_comp_eq_id s i₂ (snd A A) (lift_snd _ _))
    (unitMap_comp_eq_id s i₁ μ[A] ((Hom.mul_def _ _).symm.trans (mul_one _)))
    (unitMap_comp_eq_id s i₂ μ[A] ((Hom.mul_def _ _).symm.trans (one_mul _)))
    v.val w.val v.property w.property
  have hz : z =
      (lift (overPoint s J hJ A v) (overPoint s J hJ A w)).left := by
    apply Over.tensorObj_ext
    · exact hp.trans (by simp only [Over.lift_left, pullback.lift_fst]; rfl)
    · exact hq.trans (by simp only [Over.lift_left, pullback.lift_snd]; rfl)
  apply Over.OverMorphism.ext
  change point s J hJ A (v.val + w.val) =
    (overPoint s J hJ A v * overPoint s J hJ A w).left
  have hm' : point s J hJ A (v.val + w.val) = z ≫ μ[A].left := hm.symm
  rw [Hom.mul_def, Over.comp_left]
  exact hm'.trans (congrArg (fun t => t ≫ μ[A].left) hz)

/-- Multiplication by n on actual infinitesimal group points is n times
the corresponding tangent vector. -/
theorem overPoint_nsmul (A : Over S) [MonObj A] [IsCommMonObj A]
    (v : relative s J hJ A) (n : ℕ) :
    overPoint s J hJ A (n • v) = overPoint s J hJ A v ^ n := by
  induction n with
  | zero => simp only [zero_smul, overPoint_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, overPoint_add, ih, pow_succ]

theorem overPoint_natCast_smul (A : Over S) [MonObj A] [IsCommMonObj A]
    (v : relative s J hJ A) (n : ℕ) :
    overPoint s J hJ A ((n : C) • v) = overPoint s J hJ A v ^ n := by
  rw [Nat.cast_smul_eq_nsmul, overPoint_nsmul]

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GroupTangentsEq.Construction.GroupTangents

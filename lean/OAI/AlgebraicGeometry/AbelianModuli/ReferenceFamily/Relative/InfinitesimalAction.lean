import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.GroupTangentsEq

/-! # Infinitesimal Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.InfinitesimalAction.RelativeInfinitesimal

noncomputable section

/-! An actual integral action induces a ring representation on relative
infinitesimal points over every local coefficient ring. The ring laws
follow from the original group-scheme maps and their tangent functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {C : CommRingCat.{0}} [IsLocalRing C]
  (c : Spec C ⟶ S) (J : Ideal C) (hJ : J ^ 2 = ⊥)

abbrev Space (A : Over S) [MonObj A] := AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.relative c J hJ A

theorem tangent_mem (A B : Over S) [MonObj A] [MonObj B]
    (f : A ⟶ B) [IsMonHom f] (v : Space c J hJ A) :
    AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.tangent c J hJ f v.val ∈ AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.relative c J hJ B := by
  apply AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_injective c J hJ (𝟙_ (Over S))
  rw [AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_tangent, AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_tangent, AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_zero]
  change (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point c J hJ A v.val ≫ f.left) ≫ B.hom = c
  rw [Category.assoc, f.w]
  exact AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_over c J hJ A v

def map {A B : Over S} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f] :
    Space c J hJ A →ₗ[C] Space c J hJ B where
  toFun v := ⟨AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.tangent c J hJ f v.val, tangent_mem c J hJ A B f v⟩
  map_add' v w := Subtype.ext ((AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.tangent c J hJ f).map_add v.val w.val)
  map_smul' r v := Subtype.ext ((AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.tangent c J hJ f).map_smul r v.val)

theorem point_map {A B : Over S} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f]
    (v : Space c J hJ A) :
    AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.overPoint c J hJ B (RelativeInfinitesimal.map c J hJ f v) =
      AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.overPoint c J hJ A v ≫ f :=
  Over.OverMorphism.ext (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_tangent c J hJ f v.val)

theorem map_congr {A B : Over S} [MonObj A] [MonObj B]
    (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] (h : f = g) :
    RelativeInfinitesimal.map c J hJ f = RelativeInfinitesimal.map c J hJ g := by
  cases h
  rfl

theorem map_id (A : Over S) [MonObj A] : RelativeInfinitesimal.map c J hJ (𝟙 A) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.overPoint_injective c J hJ A
  rw [point_map, Category.comp_id]
  rfl

theorem map_comp {A B D : Over S} [MonObj A] [MonObj B] [MonObj D]
    (f : A ⟶ B) (g : B ⟶ D) [IsMonHom f] [IsMonHom g] :
    RelativeInfinitesimal.map c J hJ (f ≫ g) = (RelativeInfinitesimal.map c J hJ g).comp (RelativeInfinitesimal.map c J hJ f) := by
  apply LinearMap.ext
  intro v
  apply AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.overPoint_injective c J hJ D
  change AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.overPoint c J hJ D (RelativeInfinitesimal.map c J hJ (f ≫ g) v) =
    AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.overPoint c J hJ D (RelativeInfinitesimal.map c J hJ g (RelativeInfinitesimal.map c J hJ f v))
  rw [point_map, point_map, point_map, Category.assoc]

theorem map_one {A B : Over S} [MonObj A] [MonObj B] :
    RelativeInfinitesimal.map c J hJ (1 : A ⟶ B) = 0 := by
  apply LinearMap.ext
  intro v
  apply AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.overPoint_injective c J hJ B
  rw [point_map, MonObj.comp_one]
  exact (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.overPoint_zero c J hJ B).symm

theorem map_mul {A B : Over S} [MonObj A] [MonObj B] [IsCommMonObj B]
    (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] [IsMonHom (f * g)] :
    RelativeInfinitesimal.map c J hJ (f * g) = RelativeInfinitesimal.map c J hJ f + RelativeInfinitesimal.map c J hJ g := by
  apply LinearMap.ext
  intro v
  apply AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.overPoint_injective c J hJ B
  change AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.overPoint c J hJ B (RelativeInfinitesimal.map c J hJ (f * g) v) =
    AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.overPoint c J hJ B (RelativeInfinitesimal.map c J hJ f v + RelativeInfinitesimal.map c J hJ g v)
  rw [point_map, AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.overPoint_add, point_map, point_map, MonObj.comp_mul]

def integralAction {R : Type} [CommRing R] {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : ActionData.IntegralAction R A) : R →+* Module.End C (Space c J hJ A.scheme) where
  toFun a := RelativeInfinitesimal.map c J hJ (ρ.map a)
  map_zero' := (map_congr c J hJ (ρ.map 0) 1 ρ.map_zero).trans (RelativeInfinitesimal.map_one c J hJ)
  map_one' := (map_congr c J hJ (ρ.map 1) (𝟙 A.scheme) ρ.map_one).trans (map_id c J hJ A.scheme)
  map_add' a b := by
    let : IsMonHom (ρ.map a * ρ.map b) := by
      rw [Hom.mul_def]
      infer_instance
    exact (map_congr c J hJ (ρ.map (a + b)) (ρ.map a * ρ.map b) (ρ.map_add a b)).trans
      (RelativeInfinitesimal.map_mul c J hJ (ρ.map a) (ρ.map b))
  map_mul' a b :=
    (map_congr c J hJ (ρ.map (a * b)) (ρ.map b ≫ ρ.map a) (ρ.map_mul a b)).trans
      (map_comp c J hJ (ρ.map b) (ρ.map a))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.InfinitesimalAction.RelativeInfinitesimal

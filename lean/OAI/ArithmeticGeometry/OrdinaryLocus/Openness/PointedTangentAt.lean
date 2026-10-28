import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.InfinitesimalSchemeNe
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Pointed Tangent At -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PointedTangentAt.Construction.PointedTangent

/-!
# Openness: a functor of infinitesimal lifts for pointed schemes

An object is an actual map Spec C → X. Its tangent module consists of all
maps with the same reduction modulo a square-zero ideal. Scheme morphisms
give linear maps, with identity and composition proved via the actual maps
of schemes, not via assumed compatibility data.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {C : CommRingCat.{u}} [IsLocalRing C]
variable (J : Ideal C) (hJ : J ^ 2 = ⊥)
variable {X Y Z : Scheme.{u}}

abbrev Space (g : Spec C ⟶ X) :=
  InfinitesimalSchemeNe.Construction.InfinitesimalScheme.Lifts J hJ (Scheme.stalkClosedPointTo g)

noncomputable def point (g : Spec C ⟶ X) (v : Space J hJ g) : Spec C ⟶ X :=
  InfinitesimalSchemeNe.Construction.InfinitesimalScheme.toPoint J hJ (Scheme.stalkClosedPointTo g) v

@[simp] theorem point_zero (g : Spec C ⟶ X) : point J hJ g 0 = g := by
  change Spec.map (Scheme.stalkClosedPointTo g) ≫
    X.fromSpecStalk (g (IsLocalRing.closedPoint C)) = g
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk g

theorem point_injective (g : Spec C ⟶ X) : Function.Injective (point J hJ g) :=
  InfinitesimalSchemeNe.Construction.InfinitesimalScheme.toPoint_injective J hJ (Scheme.stalkClosedPointTo g)

theorem point_reduction (g : Spec C ⟶ X) (v : Space J hJ g) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ point J hJ g v =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ g := by
  have h := InfinitesimalSchemeNe.Construction.InfinitesimalScheme.toPoint_reduction J hJ (Scheme.stalkClosedPointTo g) v
  change _ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ point J hJ g 0 at h
  rwa [point_zero] at h

theorem exists_point (g h : Spec C ⟶ X)
    (he : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ h =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ g) :
    ∃ v : Space J hJ g, point J hJ g v = h := by
  apply InfinitesimalSchemeNe.Construction.InfinitesimalScheme.exists_stalkLift J hJ (Scheme.stalkClosedPointTo g)
  change _ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ point J hJ g 0
  rwa [point_zero]

/-- Transport along equality of base maps is a linear equivalence. -/
noncomputable def congrPoint {g h : Spec C ⟶ X} (e : g = h) :
    Space J hJ g ≃ₗ[C] Space J hJ h := by
  cases e
  exact LinearEquiv.refl C _

theorem point_congrPoint {g h : Spec C ⟶ X} (e : g = h) (v : Space J hJ g) :
    point J hJ h (congrPoint J hJ e v) = point J hJ g v := by
  cases e
  rfl

/-- Transport along equality of the local base ring map. -/
noncomputable def congrGerm {x : X} {e f : X.presheaf.stalk x ⟶ C} (h : e = f) :
    InfinitesimalSchemeNe.Construction.InfinitesimalScheme.Lifts J hJ e ≃ₗ[C] InfinitesimalSchemeNe.Construction.InfinitesimalScheme.Lifts J hJ f := by
  cases h
  exact LinearEquiv.refl C _

omit [IsLocalRing C] in
theorem point_congrGerm {x : X} {e f : X.presheaf.stalk x ⟶ C} (h : e = f)
    (v : InfinitesimalSchemeNe.Construction.InfinitesimalScheme.Lifts J hJ e) :
    InfinitesimalSchemeNe.Construction.InfinitesimalScheme.toPoint J hJ f (congrGerm J hJ h v) =
      InfinitesimalSchemeNe.Construction.InfinitesimalScheme.toPoint J hJ e v := by
  cases h
  rfl

/-- The linear map induced by postcomposing with a scheme morphism. -/
noncomputable def mapAt (g : Spec C ⟶ X) (q : X ⟶ Y) :
    Space J hJ g →ₗ[C] Space J hJ (g ≫ q) :=
  (congrGerm J hJ (Scheme.stalkClosedPointTo_comp g q).symm).toLinearMap.comp
    (InfinitesimalSchemeNe.Construction.InfinitesimalScheme.map J hJ (Scheme.stalkClosedPointTo g) q)

theorem point_mapAt (g : Spec C ⟶ X) (q : X ⟶ Y) (v : Space J hJ g) :
    point J hJ (g ≫ q) (mapAt J hJ g q v) = point J hJ g v ≫ q := by
  exact (point_congrGerm J hJ (Scheme.stalkClosedPointTo_comp g q).symm
    (InfinitesimalSchemeNe.Construction.InfinitesimalScheme.map J hJ (Scheme.stalkClosedPointTo g) q v)).trans
      (InfinitesimalSchemeNe.Construction.InfinitesimalScheme.toPoint_map J hJ (Scheme.stalkClosedPointTo g) q v)

/-- Morphisms in the category of pointed schemes act linearly on lift modules. -/
noncomputable def map {P Q : Under (Spec C)} (f : P ⟶ Q) :
    Space J hJ P.hom →ₗ[C] Space J hJ Q.hom :=
  (congrPoint J hJ (Under.w f)).toLinearMap.comp (mapAt J hJ P.hom f.right)

theorem point_map {P Q : Under (Spec C)} (f : P ⟶ Q) (v : Space J hJ P.hom) :
    point J hJ Q.hom (PointedTangent.map J hJ f v) = point J hJ P.hom v ≫ f.right := by
  exact (point_congrPoint J hJ (Under.w f) (mapAt J hJ P.hom f.right v)).trans
    (point_mapAt J hJ P.hom f.right v)

theorem map_id (P : Under (Spec C)) : PointedTangent.map J hJ (𝟙 P) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply point_injective J hJ P.hom
  rw [point_map]
  simp only [Under.id_right, Category.comp_id, LinearMap.id_apply]

theorem map_comp {P Q R : Under (Spec C)} (f : P ⟶ Q) (g : Q ⟶ R) :
    PointedTangent.map J hJ (f ≫ g) = (PointedTangent.map J hJ g).comp (PointedTangent.map J hJ f) := by
  apply LinearMap.ext
  intro v
  apply point_injective J hJ R.hom
  change point J hJ R.hom (PointedTangent.map J hJ (f ≫ g) v) =
    point J hJ R.hom (PointedTangent.map J hJ g (PointedTangent.map J hJ f v))
  rw [point_map, point_map, point_map, Under.comp_right, Category.assoc]

/-- The intrinsic infinitesimal-lift functor on all pointed schemes. -/
noncomputable def tangentFunctor : Under (Spec C) ⥤ ModuleCat C where
  obj P := ModuleCat.of C (Space J hJ P.hom)
  map f := ModuleCat.ofHom (PointedTangent.map J hJ f)
  map_id P := by
    apply ModuleCat.hom_ext
    exact PointedTangent.map_id J hJ P
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact PointedTangent.map_comp J hJ f g

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PointedTangentAt.Construction.PointedTangent

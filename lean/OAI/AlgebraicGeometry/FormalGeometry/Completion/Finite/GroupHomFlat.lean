import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.GenericFlatness
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FlatTranslation
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Group Hom Flat -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.GroupHomFlat.Construction

noncomputable section

/-! A finite surjective homomorphism of geometric algebraic groups is flat over a smooth target. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]

/-- An actual group homomorphism intertwines translation with translation by the image point. -/
theorem groupHom_translation (f : A ⟶ B) [IsMonHom f] (b : 𝟙_ (Over S) ⟶ A) :
    (GrpObj.mulRight b).hom ≫ f = f ≫ (GrpObj.mulRight (b ≫ f)).hom := by
  change (𝟙 A * (toUnit A ≫ b)) ≫ f = f ≫ (𝟙 B * (toUnit B ≫ (b ≫ f)))
  rw [MonObj.mul_comp, Category.id_comp, MonObj.comp_mul, Category.comp_id]
  simp only [← Category.assoc, comp_toUnit]

variable {K : Type u} [Field K] [IsAlgClosed K]
  {A B : Over (Spec (CommRingCat.of K))} [GrpObj A] [GrpObj B]
  [LocallyOfFiniteType A.hom]

/-- Translation gives commuting automorphisms carrying any closed source point to another. -/
theorem groupHom_transitive_automorphisms (f : A ⟶ B) [IsMonHom f]
    (x y : A.left) (hx : IsClosed {x}) (hy : IsClosed {y}) :
    ∃ (α : A.left ≅ A.left) (β : B.left ≅ B.left),
      α.hom x = y ∧ α.hom ≫ f.left = f.left ≫ β.hom := by
  let x' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom x hx) (pointOfClosedPoint_comp A.hom x hx)
  let y' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom y hy) (pointOfClosedPoint_comp A.hom y hy)
  let b := x'⁻¹ * y'
  let α := (Over.forget _).mapIso (GrpObj.mulRight b)
  let β := (Over.forget _).mapIso (GrpObj.mulRight (b ≫ f))
  have hxy : x' ≫ (GrpObj.mulRight b).hom = y' := by
    change x' ≫ (𝟙 A * (toUnit A ≫ b)) = y'
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
      comp_toUnit, toUnit_unit, Category.id_comp]
    exact mul_inv_cancel_left x' y'
  refine ⟨α, β, ?_, congrArg Over.Hom.left (groupHom_translation f b)⟩
  have h : x'.left ≫ α.hom = y'.left := congrArg Over.Hom.left hxy
  have he := congrArg (fun z : Spec (CommRingCat.of K) ⟶ A.left =>
    z (IsLocalRing.closedPoint K)) h
  change α.hom (x'.left (IsLocalRing.closedPoint K)) = y'.left (IsLocalRing.closedPoint K) at he
  have hx' : x'.left (IsLocalRing.closedPoint K) = x := pointOfClosedPoint_apply A.hom x hx _
  have hy' : y'.left (IsLocalRing.closedPoint K) = y := pointOfClosedPoint_apply A.hom y hy _
  rw [hx', hy'] at he
  exact he

/-- Generic freeness and group translations prove flatness of the actual finite surjective map. -/
theorem finite_surjective_groupHom_flat [Smooth B.hom]
    (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Surjective f.left] : Flat f.left := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have : IsReduced B.left := Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_smooth_field B.hom
  have : Nonempty B.left := ⟨(η[B]).left (IsLocalRing.closedPoint K)⟩
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  obtain ⟨U, hU, hflat⟩ := GenericFlatness.Construction.exists_nonempty_flat_source_open_of_reduced f.left
  have : Flat (U.ι ≫ f.left) := hflat
  exact FlatTranslation.Construction.flat_of_transitive_automorphisms f.left (groupHom_transitive_automorphisms f) U hU

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.GroupHomFlat.Construction

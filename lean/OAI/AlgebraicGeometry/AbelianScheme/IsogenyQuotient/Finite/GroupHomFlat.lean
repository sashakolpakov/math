import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationFlat

/-! # Group Hom Flat -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.GroupHomFlat.Construction

noncomputable section

/-!
Finite surjective homomorphisms between smooth group schemes are flat.
Translations spread generic flatness across each geometric fiber, and
the existing finite-morphism criterion descends flatness to the base.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem groupHom_translation
    {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
    (f : A ⟶ B) [IsMonHom f] (b : 𝟙_ (Over S) ⟶ A) :
    (GrpObj.mulRight b).hom ≫ f = f ≫ (GrpObj.mulRight (b ≫ f)).hom := by
  change ((𝟙 A) * (toUnit A ≫ b)) ≫ f = f ≫ ((𝟙 B) * (toUnit B ≫ b ≫ f))
  rw [MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id]
  rw [Category.assoc, ← Category.assoc f (toUnit B), comp_toUnit]

theorem groupHom_transitive_automorphisms
    {k : Type u} [Field k] [IsAlgClosed k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
    [LocallyOfFiniteType A.hom] (f : A ⟶ B) [IsMonHom f]
    (x y : A.left) (hx : IsClosed {x}) (hy : IsClosed {y}) :
    ∃ (α : A.left ≅ A.left) (β : B.left ≅ B.left),
      α.hom x = y ∧ α.hom ≫ f.left = f.left ≫ β.hom := by
  let x' : 𝟙_ (Over (Spec (.of k))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom x hx) (pointOfClosedPoint_comp A.hom x hx)
  let y' : 𝟙_ (Over (Spec (.of k))) ⟶ A :=
    Over.homMk (pointOfClosedPoint A.hom y hy) (pointOfClosedPoint_comp A.hom y hy)
  let b := x'⁻¹ * y'
  let α := (Over.forget (Spec (.of k))).mapIso (GrpObj.mulRight b)
  let β := (Over.forget (Spec (.of k))).mapIso (GrpObj.mulRight (b ≫ f))
  have hxy : x' ≫ (GrpObj.mulRight b).hom = y' := by
    change x' ≫ ((𝟙 A) * (toUnit A ≫ b)) = y'
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
      comp_toUnit, toUnit_unit, Category.id_comp]
    exact mul_inv_cancel_left x' y'
  refine ⟨α, β, ?_, congrArg Over.Hom.left (groupHom_translation f b)⟩
  have h : x'.left ≫ α.hom = y'.left := congrArg Over.Hom.left hxy
  have heval := congrArg (fun z : Spec (.of k) ⟶ A.left => z (IsLocalRing.closedPoint k)) h
  change α.hom (x'.left (IsLocalRing.closedPoint k)) = y'.left (IsLocalRing.closedPoint k) at heval
  have hx' : x'.left (IsLocalRing.closedPoint k) = x := pointOfClosedPoint_apply A.hom x hx _
  have hy' : y'.left (IsLocalRing.closedPoint k) = y := pointOfClosedPoint_apply A.hom y hy _
  rwa [hx', hy'] at heval

theorem finite_surjective_groupHom_flat_geometric
    {k : Type u} [Field k] [IsAlgClosed k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
    [Smooth A.hom] [Smooth B.hom] (f : A ⟶ B) [IsMonHom f]
    [IsFinite f.left] [Surjective f.left] : Flat f.left := by
  have : IsReduced B.left := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field B.hom
  have : Nonempty B.left := ⟨η[B].left (IsLocalRing.closedPoint k)⟩
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have hfp : LocallyOfFinitePresentation (f.left ≫ B.hom) := by rw [f.w]; infer_instance
  have : LocallyOfFinitePresentation f.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType hfp inferInstance
  obtain ⟨U, hU, hflat⟩ := CartierDuality.GenericFlat.Construction.GenericFlatOpen.exists_nonempty_flat_source_open_of_reduced f.left
  have : Flat (U.ι ≫ f.left) := hflat
  exact CartierDuality.MultiplicationFlat.Construction.Multiplication.flat_of_transitive_automorphisms f.left
    (groupHom_transitive_automorphisms f) U hU

theorem finite_surjective_groupHom_flat
    {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
    [Smooth A.hom] [Smooth B.hom] (f : A ⟶ B) [IsMonHom f]
    [IsFinite f.left] [Surjective f.left] : Flat f.left := by
  have hfp : LocallyOfFinitePresentation (f.left ≫ B.hom) := by rw [f.w]; infer_instance
  have : LocallyOfFinitePresentation f.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType hfp inferInstance
  apply ArithmeticGeometry.OrdinaryLocus.Openness.FiberwiseFlatness.Construction.flat_finite_of_flat_geometric_baseChanges f
  intro k _ _ s
  let F := Over.pullback s
  have : Smooth (F.obj A).hom := inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd A.hom s))
  have : Smooth (F.obj B).hom := inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd B.hom s))
  have : IsFinite (F.map f).left := MorphismProperty.overPullbackMap (P := @IsFinite) s f inferInstance
  have : Surjective (F.map f).left := MorphismProperty.overPullbackMap (P := @Surjective) s f inferInstance
  exact finite_surjective_groupHom_flat_geometric (F.map f)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.GroupHomFlat.Construction

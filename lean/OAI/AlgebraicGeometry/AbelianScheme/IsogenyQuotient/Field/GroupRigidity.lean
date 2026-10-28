import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison
import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupDescent
import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDualData

/-! # Group Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.GroupRigidity.Construction

noncomputable section

/-!
Group-law rigidity descends from an algebraic closure along a faithfully
flat base change. Thus the original normalized Picard representation has
its given group law over every field, with no characteristic restriction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem isMonHom_of_faithful_monoidal_map
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] [F.Faithful] {X Y : C} [MonObj X] [MonObj Y]
    (f : X ⟶ Y) [IsMonHom (F.map f)] : IsMonHom f where
  one_hom := by
    apply F.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.ε F)).mp
    have h := IsMonHom.one_hom (F.map f)
    change (Functor.LaxMonoidal.ε F ≫ F.map MonObj.one) ≫ F.map f =
      Functor.LaxMonoidal.ε F ≫ F.map MonObj.one at h
    simpa only [Category.assoc, F.map_comp] using h
  mul_hom := by
    apply F.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.μ F X X)).mp
    have h := IsMonHom.mul_hom (F.map f)
    change (Functor.LaxMonoidal.μ F X X ≫ F.map MonObj.mul) ≫ F.map f =
      (F.map f ⊗ₘ F.map f) ≫ Functor.LaxMonoidal.μ F Y Y ≫ F.map MonObj.mul at h
    rw [Functor.LaxMonoidal.μ_natural_assoc] at h
    simpa only [Category.assoc, F.map_comp] using h

theorem pointed_isMonHom_over_field
    {k : Type u} [Field k]
    (A B : Over (Spec (.of k))) [groupA : GrpObj A] [commA : IsCommMonObj A] [groupB : GrpObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [LocallyOfFiniteType B.hom] [IsSeparated B.hom]
    (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) : IsMonHom f := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have : Flat s := inferInstanceAs
    (Flat (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
  have : Surjective s := ⟨Function.surjective_to_subsingleton _⟩
  have : QuasiCompact s := inferInstanceAs
    (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
  have (Z : Scheme.{u}) (g : Z ⟶ Spec (.of k)) : Epi (pullback.fst g s) := inferInstance
  let F := Over.pullback s
  have : F.Faithful := inferInstance
  let A' := F.obj A
  let B' := F.obj B
  have : Smooth A'.hom := inferInstanceAs (Smooth (pullback.snd A.hom s))
  have : IsProper A'.hom := inferInstanceAs (IsProper (pullback.snd A.hom s))
  have : GeometricallyConnected A'.hom := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom s))
  have : LocallyOfFiniteType B'.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd B.hom s))
  have : IsSeparated B'.hom := inferInstanceAs (IsSeparated (pullback.snd B.hom s))
  have hunit : η[A'] ≫ F.map f = η[B'] := by
    change (Functor.LaxMonoidal.ε F ≫ F.map η[A]) ≫ F.map f =
      Functor.LaxMonoidal.ε F ≫ F.map η[B]
    rw [Category.assoc, ← F.map_comp, hf]
  have : IsMonHom (F.map f) := Picard.Homomorphisms.GroupRigidity.Construction.pointed_isMonHom A' B' (F.map f) hunit
  exact isMonHom_of_faithful_monoidal_map F f

theorem groupStructure_eq_of_origin_over_field
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    (G H : GrpObj X) (hcomm : letI := G; IsCommMonObj X)
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    (hunit : G.toMonObj.one = H.toMonObj.one) : G = H := by
  have h := pointed_isMonHom_over_field (groupA := G) (commA := hcomm) (groupB := H) X X (𝟙 X)
    ((Category.comp_id G.toMonObj.one).trans hunit)
  have hm := @IsMonHom.mul_hom _ _ _ _ _ G.toMonObj H.toMonObj (𝟙 X) h
  have hmul : G.toMonObj.mul = H.toMonObj.mul := by
    simpa only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp] using hm
  exact GrpObj.ext G H (Picard.Homomorphisms.DualGroupComparison.Construction.monObj_eq_of_operations G.toMonObj H.toMonObj hunit hmul)

theorem dualPicardGroup_eq_given_over_field
    {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) :
    Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D = D.group :=
  groupStructure_eq_of_origin_over_field D.abelian _ _
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D)
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_origin D)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.GroupRigidity.Construction

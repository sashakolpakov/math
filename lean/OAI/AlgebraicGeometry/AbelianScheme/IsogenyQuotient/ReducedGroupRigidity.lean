import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.GroupRigidity
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth

/-! # Reduced Group Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ReducedGroupRigidity.Construction

noncomputable section

/-!
Field-valued base changes detect maps from a reduced scheme. Applied to
the multiplication diagram, this identifies the two dual group laws
over reduced locally Noetherian bases. Reducedness is an explicit
hypothesis; the lemma does not discard infinitesimal test schemes.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem overHom_eq_of_field_baseChanges
    {S : Scheme.{u}} {X Y : Over S} [IsReduced X.left] [IsSeparated Y.hom]
    (f g : X ⟶ Y)
    (h : ∀ (k : Type u) [Field k] (s : Spec (.of k) ⟶ S),
      (Over.pullback s).map f = (Over.pullback s).map g) : f = g := by
  ext1
  apply ext_of_fromSpecResidueField_eq f.left g.left Y.hom Set.univ dense_univ
  · intro x _
    let a := X.left.fromSpecResidueField x
    let s := a ≫ X.hom
    let l : Spec (X.left.residueField x) ⟶ pullback X.hom s :=
      pullback.lift a (𝟙 _) (by simp [s])
    have H := congrArg (fun z => l ≫ z.left ≫ pullback.fst Y.hom s)
      (h (X.left.residueField x) s)
    simpa only [Over.pullback_map_left, ← Category.assoc, l, pullback.lift_fst, a] using H
  · exact (Over.w f).trans (Over.w g).symm

theorem pointed_isMonHom_of_reduced_square
    {S : Scheme.{u}} (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [LocallyOfFiniteType B.hom] [IsSeparated B.hom] [IsReduced (A ⊗ A).left]
    (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) : IsMonHom f := by
  refine ⟨hf, ?_⟩
  apply overHom_eq_of_field_baseChanges
  intro k _ s
  let F := Over.pullback s
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
  have : IsMonHom (F.map f) := IsogenyQuotient.Field.GroupRigidity.Construction.pointed_isMonHom_over_field A' B' (F.map f) hunit
  change F.map (μ[A] ≫ f) = F.map ((f ⊗ₘ f) ≫ μ[B])
  apply (cancel_epi (Functor.LaxMonoidal.μ F A A)).mp
  have hmul := IsMonHom.mul_hom (F.map f)
  change (Functor.LaxMonoidal.μ F A A ≫ F.map μ[A]) ≫ F.map f =
    (F.map f ⊗ₘ F.map f) ≫ Functor.LaxMonoidal.μ F B B ≫ F.map μ[B] at hmul
  rw [Functor.LaxMonoidal.μ_natural_assoc] at hmul
  simpa only [Category.assoc, F.map_comp] using hmul

theorem pointed_isMonHom_over_reduced_base
    {S : Scheme.{u}} [IsReduced S] [IsLocallyNoetherian S]
    (A B : Over S) [groupA : GrpObj A] [commA : IsCommMonObj A] [groupB : GrpObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [LocallyOfFiniteType B.hom] [IsSeparated B.hom]
    (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) : IsMonHom f := by
  have : Smooth (A ⊗ A).hom := by dsimp; infer_instance
  have : GeometricallyReduced (A ⊗ A).hom :=
    Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.geometricallyReduced_of_smooth (A ⊗ A).hom
  have : IsReduced (A ⊗ A).left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (A ⊗ A).hom
  exact pointed_isMonHom_of_reduced_square A B f hf

theorem groupStructure_eq_of_origin_over_reduced_base
    {S : Scheme.{u}} [IsReduced S] [IsLocallyNoetherian S] (X : Over S)
    (G H : GrpObj X) (hcomm : letI := G; IsCommMonObj X)
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    (hunit : G.toMonObj.one = H.toMonObj.one) : G = H := by
  have h := pointed_isMonHom_over_reduced_base (groupA := G) (commA := hcomm) (groupB := H) X X (𝟙 X)
    ((Category.comp_id G.toMonObj.one).trans hunit)
  have hm := @IsMonHom.mul_hom _ _ _ _ _ G.toMonObj H.toMonObj (𝟙 X) h
  have hmul : G.toMonObj.mul = H.toMonObj.mul := by
    simpa only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp] using hm
  exact GrpObj.ext G H (Picard.Homomorphisms.DualGroupComparison.Construction.monObj_eq_of_operations G.toMonObj H.toMonObj hunit hmul)

theorem dualPicardGroup_eq_given_over_reduced_base
    {S : Scheme.{u}} [IsReduced S] [IsLocallyNoetherian S] {A : Over S} [GrpObj A]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) :
    Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D = D.group :=
  groupStructure_eq_of_origin_over_reduced_base D.abelian _ _
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D)
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_origin D)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ReducedGroupRigidity.Construction

import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PointGroupDetection

/-! # Group Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.GroupRigidity.Construction

noncomputable section

/-! Function rigidity on the square of a proper smooth connected
group identifies every pointed map with a group homomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem pointed_isMonHom_of_square_functions
    {S : Scheme.{u}} (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [LocallyOfFiniteType B.hom] [IsSeparated B.hom]
    (hΓ : ∀ V : S.Opens, IsIso ((A ⊗ A).hom ∣_ V).appTop)
    (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) : IsMonHom f := by
  let u : A ⊗ A ⟶ B := μ[A] ≫ f
  let v : A ⊗ A ⟶ B := (fst A A ≫ f) * (snd A A ≫ f)
  have hfield : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ S),
      (Over.pullback s).map u = (Over.pullback s).map v := by
    intro K _ s
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
  let d : A ⊗ A ⟶ B := u / v
  have hηu : η[A ⊗ A] ≫ u = η[B] := by
    dsimp only [u]
    rw [← Category.assoc, IsMonHom.one_hom, hf]
  have hηv : η[A ⊗ A] ≫ v = η[B] := by
    dsimp only [v]
    rw [MonObj.comp_mul, ← Category.assoc, IsMonHom.one_hom, hf,
      ← Category.assoc, IsMonHom.one_hom, hf]
    change (1 : 𝟙_ (Over S) ⟶ B) * 1 = 1
    exact one_mul _
  have hzero : η[A ⊗ A] ≫ d = η[B] := by
    rw [show d = u / v from rfl, GrpObj.comp_div, hηu, hηv, div_self']
    simp [Hom.one_def]
  have : IsProper (A ⊗ A).hom := by dsimp; infer_instance
  have hd : d = 1 := IsogenyQuotient.Field.PointGroupDetection.Construction.overHom_eq_one_of_fieldPoints (A ⊗ A) B hΓ d hzero (by
    intro K _ s x
    rw [show d = u / v from rfl, GrpObj.comp_div,
      IsogenyQuotient.Field.PointGroupDetection.Construction.overHom_fieldPoint_eq_of_field_baseChanges u v hfield s x, div_self'])
  refine ⟨hf, ?_⟩
  have hm := div_eq_one.mp hd
  change μ[A] ≫ f = (fst A A ≫ f) * (snd A A ≫ f) at hm
  rw [hm, Hom.mul_def]
  congr 1

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.GroupRigidity.Construction

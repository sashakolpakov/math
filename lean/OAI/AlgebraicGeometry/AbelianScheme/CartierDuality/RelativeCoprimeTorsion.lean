import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GeometricIsomorphisms
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TorsionBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Torsion

/-! # Relative Coprime Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeCoprimeTorsion.Construction.CoprimeTorsion

noncomputable section

/-!
# CartierDuality: arbitrary-base coprime isogenies on actual torsion
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

/-- The zero section of the pulled-back native group projects to the
original zero section. -/
theorem baseChange_zero {S T : Scheme.{u}} (a : T ⟶ S) (B : Over S) [GrpObj B] :
    η[(Over.pullback a).obj B].left ≫ pullback.fst B.hom a = a ≫ η[B].left := by
  let F := Over.pullback a
  have hη : η[F.obj B].left ≫ pullback.fst B.hom a =
      (Functor.LaxMonoidal.ε F).left ≫ pullback.fst (𝟙 S) a ≫ η[B].left := by
    change (Functor.LaxMonoidal.ε F ≫ F.map η[B]).left ≫ pullback.fst B.hom a = _
    simp only [Over.comp_left, Category.assoc, F, Over.pullback_map_left, pullback.lift_fst]
    rfl
  have hp : pullback.fst (𝟙 S) a = pullback.snd (𝟙 S) a ≫ a := by
    simpa only [Category.comp_id] using (pullback.condition (f := 𝟙 S) (g := a))
  have he : (Functor.LaxMonoidal.ε F).left ≫ pullback.snd (𝟙 S) a = 𝟙 T := by
    rw [Over.ε_pullback_left, IsIso.inv_hom_id]
    rfl
  rw [hη, hp]
  simp only [← Category.assoc, he]
  exact congrArg (fun q : T ⟶ S => q ≫ η[B].left) (Category.id_comp a)

/-- Degree along the zero section commutes with arbitrary base change. -/
theorem degree_baseChange {S T : Scheme.{u}} (a : T ⟶ S)
    {A B : Over S} [GrpObj B] (f : A ⟶ B) [IsFinite f.left] [Flat f.left] (t : T) :
    ((Over.pullback a).map f).left.finrank (η[(Over.pullback a).obj B].left t) =
      f.left.finrank (η[B].left (a t)) := by
  have hr := Scheme.Hom.finrank_of_isPullback _ _ _ _
    (LocalIsomorphismsIs.Construction.LocalIsomorphisms.pullbackMap_isPullback a f) (η[(Over.pullback a).obj B].left t)
  have hz : pullback.fst B.hom a (η[(Over.pullback a).obj B].left t) = η[B].left (a t) :=
    congrArg (fun q : T ⟶ B.left => q t) (baseChange_zero a B)
  exact hr.trans (congrArg (fun b => f.left.finrank b) hz)

/-- Fiberwise coprimality with the actual degree makes a finite-flat
surjective homomorphism an isomorphism on finite locally free n-torsion. -/
theorem torsionMap_isIso_of_coprime_fiber_degree
    {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
    [IsCommMonObj A] [IsCommMonObj B] (f : A ⟶ B) [IsMonHom f]
    [IsFinite f.left] [Flat f.left] [Surjective f.left] (n : ℕ)
    [IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom] [Flat (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom]
    [LocallyOfFinitePresentation (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom]
    [IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme B n).hom] [Flat (TorsionQuotient.SubgroupFunctor.torsionScheme B n).hom]
    [LocallyOfFinitePresentation (TorsionQuotient.SubgroupFunctor.torsionScheme B n).hom]
    (hdegree : ∀ s : S, n.Coprime (f.left.finrank (η[B].left s))) :
    IsIso (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n) := by
  have hi : IsIso (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n).left := GeometricIsomorphisms.Construction.Schemes.isIso_of_algClosed_baseChanges (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n) (by
    intro K _ _ a
    let F := Over.pullback a
    let f' := F.map f
    have : IsFinite f'.left := MorphismProperty.overPullbackMap (P := @IsFinite) a f inferInstance
    have : Flat f'.left := MorphismProperty.overPullbackMap (P := @Flat) a f inferInstance
    have : Surjective f'.left := MorphismProperty.overPullbackMap (P := @Surjective) a f inferInstance
    have hc : n.Coprime (f'.left.finrank (η[F.obj B].left (IsLocalRing.closedPoint K))) := by
      have hd := degree_baseChange a f (show Spec (.of K) from IsLocalRing.closedPoint K)
      exact hd.symm ▸ hdegree (a (IsLocalRing.closedPoint K))
    have : IsIso (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f' n) := CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap_isIso_of_coprime_degree f' n (IsLocalRing.closedPoint K) hc
    exact TorsionBaseChange.Construction.CoprimeTorsion.torsionMap_baseChange_isIso a n f)
  have : IsIso ((Over.forget S).map (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n)) := hi
  exact isIso_of_reflects_iso (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n) (Over.forget S)

/-- For abelian schemes with their actual dual, the degree hypothesis
alone suffices: finite local freeness of both torsion schemes is proved. -/
theorem abelian_torsionMap_isIso
    {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
    (n : ℕ) (hn : 0 < n)
    (hdegree : ∀ s : S, n.Coprime (ell.hom.left.finrank (η[D.abelian.scheme].left s))) :
    IsIso (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap ell.hom n) := by
  have : IsFinite ((𝟙 A.scheme) ^ n).left := Torsion.Construction.Multiplication.finite_positive_power A D ell n hn
  have : IsFinite ((𝟙 D.abelian.scheme) ^ n).left := Torsion.Construction.Multiplication.finite_positive_dual_power A D n hn
  obtain ⟨hAf, hAflat, hAfp⟩ := TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk A.scheme) n
  obtain ⟨hBf, hBflat, hBfp⟩ := TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk D.abelian.scheme) n
  exact torsionMap_isIso_of_coprime_fiber_degree ell.hom n hdegree

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeCoprimeTorsion.Construction.CoprimeTorsion

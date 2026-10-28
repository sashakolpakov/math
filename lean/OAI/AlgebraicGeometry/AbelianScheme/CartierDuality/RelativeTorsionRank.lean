import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IsogenyTorsionRank
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Rank

/-! # Relative Torsion Rank -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeTorsionRank

noncomputable section

/-! Torsion ranks on the geometric fibers of a relative isogeny. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.Schemes

/-- Finiteness of multiplication is preserved by arbitrary base change. -/
theorem finite_power_baseChange {S T : Scheme.{u}} (s : T ⟶ S)
    (A : Over S) [GrpObj A] (n : ℕ) [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] :
    IsFinite ((𝟙 ((Over.pullback s).obj A) : (Over.pullback s).obj A ⟶ (Over.pullback s).obj A) ^ n).left := by
  have hf : IsFinite ((Over.pullback s).map ((𝟙 A : A ⟶ A) ^ n)).left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) s _ inferInstance
  exact (congrArg (fun q => q.left) (TorsionBaseChange.Construction.CoprimeTorsion.power_baseChange s A n)) ▸ hf

/-- The two actual relative torsion schemes have equal ranks on every geometric fiber. -/
theorem geometric_torsion_finrank_eq_of_isogeny
    {S : Scheme.{u}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [Smooth B.hom] [IsProper B.hom] [GeometricallyConnected B.hom]
    (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left]
    (n : ℕ) [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] [IsFinite ((𝟙 B : B ⟶ B) ^ n).left]
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) (t : Spec (.of k)) :
    ((Over.pullback s).obj (TorsionQuotient.SubgroupFunctor.torsionScheme A n)).hom.finrank t =
      ((Over.pullback s).obj (TorsionQuotient.SubgroupFunctor.torsionScheme B n)).hom.finrank t := by
  let A' := (Over.pullback s).obj A
  let B' := (Over.pullback s).obj B
  have : Smooth A'.hom := inferInstanceAs (Smooth (pullback.snd A.hom s))
  have : IsProper A'.hom := inferInstanceAs (IsProper (pullback.snd A.hom s))
  have : GeometricallyConnected A'.hom := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom s))
  have : Smooth B'.hom := inferInstanceAs (Smooth (pullback.snd B.hom s))
  have : IsProper B'.hom := inferInstanceAs (IsProper (pullback.snd B.hom s))
  have : GeometricallyConnected B'.hom := inferInstanceAs (GeometricallyConnected (pullback.snd B.hom s))
  have : IsFinite ((𝟙 A' : A' ⟶ A') ^ n).left := finite_power_baseChange s A n
  have : IsFinite ((𝟙 B' : B' ⟶ B') ^ n).left := finite_power_baseChange s B n
  have hf : IsFinite ((Over.pullback s).map f).left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) s _ inferInstance
  have hflat : Flat ((Over.pullback s).map f).left :=
    MorphismProperty.overPullbackMap (P := @Flat) s _ inferInstance
  have hs : Surjective ((Over.pullback s).map f).left :=
    MorphismProperty.overPullbackMap (P := @Surjective) s _ inferInstance
  have hA := TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk A') n
  have hB := TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk B') n
  have : IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A' n).hom := hA.1
  have : Flat (TorsionQuotient.SubgroupFunctor.torsionScheme A' n).hom := hA.2.1
  have : IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme B' n).hom := hB.1
  have : Flat (TorsionQuotient.SubgroupFunctor.torsionScheme B' n).hom := hB.2.1
  exact (Rank.Construction.Schemes.overIso_finrank (TorsionBaseChange.Construction.CoprimeTorsion.torsionBaseChangeIso s A n) t).trans
    ((IsogenyTorsionRank.Construction.Schemes.torsionKernel_finrank_eq_of_isogeny A' B' ((Over.pullback s).map f) n t).trans
      (Rank.Construction.Schemes.overIso_finrank (TorsionBaseChange.Construction.CoprimeTorsion.torsionBaseChangeIso s B n) t).symm)

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeTorsionRank

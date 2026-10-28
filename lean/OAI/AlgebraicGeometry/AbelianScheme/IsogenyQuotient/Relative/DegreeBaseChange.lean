import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.DegreeLoci
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LocalIsomorphismsIs

/-! # Degree Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.DegreeBaseChange.Construction

noncomputable section

/-! Restriction to the base's actual degree loci gives constant-degree
finite-flat maps. Positive degrees are units on schemes over a field
of characteristic zero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {X A : Over S} [GrpObj A] [GeometricallyConnected A.hom]
  (f : X ⟶ A) [IsFinite f.left] [Flat f.left] [LocallyOfFinitePresentation f.left]

theorem degreeLocus_pullback_finrank (d : ℕ)
    (a : ((Over.pullback (DegreeLoci.Construction.relativeDegreeOpen f d).ι).obj A).left) :
    ((Over.pullback (DegreeLoci.Construction.relativeDegreeOpen f d).ι).map f).left.finrank a = d := by
  let t := (DegreeLoci.Construction.relativeDegreeOpen f d).ι
  have hp := CartierDuality.LocalIsomorphismsIs.Construction.LocalIsomorphisms.pullbackMap_isPullback t f
  have hw : A.hom (pullback.fst A.hom t a) = t (pullback.snd A.hom t a) :=
    congrArg (fun m => m a) (pullback.condition (f := A.hom) (g := t))
  exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ hp a).trans
    ((DegreeLoci.Construction.finiteFlatDegree_eq_base_degree f (pullback.fst A.hom t a)).trans
      ((congrArg (DegreeLoci.Construction.relativeFiniteFlatDegree f) hw).trans (pullback.snd A.hom t a).property))

omit [GeometricallyConnected A.hom] [LocallyOfFinitePresentation f.left] in
theorem relativeDegree_pos [Surjective f.left] (s : S) : 0 < DegreeLoci.Construction.relativeFiniteFlatDegree f s :=
  (Scheme.Hom.one_le_finrank_iff_surjective f.left).mpr inferInstance (η[A].left s)

omit [GeometricallyConnected A.hom] in
theorem degreeLocus_degree_pos [Surjective f.left] {d : ℕ} (s : DegreeLoci.Construction.relativeDegreeOpen f d) : 0 < d :=
  s.property ▸ relativeDegree_pos f s.val

theorem positiveNat_isUnit_on_charZero_field_scheme
    {k : Type u} [Field k] [CharZero k] {S : Scheme.{u}} (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (s : S) : IsUnit (n : S.presheaf.stalk s) := by
  let c : CommRingCat.of k ⟶ S.presheaf.stalk s :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ S.presheaf.germ ⊤ s trivial
  have hu : IsUnit (n : k) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
  simpa only [map_natCast] using hu.map c.hom

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.DegreeBaseChange.Construction

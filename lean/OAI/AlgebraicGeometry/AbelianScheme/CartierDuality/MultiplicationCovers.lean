import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeTorsion

/-! # Multiplication Covers -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationCovers

noncomputable section

/-!
# CartierDuality: positive multiplication gives an actual faithfully flat cover
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.Schemes

/-- Surjectivity is detected after every algebraically closed field
base change, with no assumptions on the original base scheme. -/
theorem surjective_of_algClosed_baseChanges {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S),
      Surjective ((Over.pullback a).map f).left) : Surjective f.left := by
  constructor
  intro y
  let K := AlgebraicClosure (Y.left.residueField y)
  let v : Spec (.of K) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) K)) ≫
      Y.left.fromSpecResidueField y
  let a := v ≫ Y.hom
  let j : Spec (.of K) ⟶ pullback Y.hom a := pullback.lift v (𝟙 _) (by simp [a])
  let y' := j (IsLocalRing.closedPoint K)
  have hy : pullback.fst Y.hom a y' = y := by
    have hj : j ≫ pullback.fst Y.hom a = v := pullback.lift_fst _ _ _
    have hv : v (IsLocalRing.closedPoint K) = y := Y.left.fromSpecResidueField_apply y _
    exact (congrArg (fun g : Spec (.of K) ⟶ Y.left => g (IsLocalRing.closedPoint K)) hj).trans hv
  let fp := ((Over.pullback a).map f).left
  have : Surjective fp := h K a
  obtain ⟨x, hx⟩ := fp.surjective y'
  refine ⟨pullback.fst X.hom a x, ?_⟩
  have hs : pullback.fst X.hom a ≫ f.left = fp ≫ pullback.fst Y.hom a :=
    (LocalIsomorphismsIs.Construction.LocalIsomorphisms.pullbackMap_isPullback a f).w
  exact (congrArg (fun g : pullback X.hom a ⟶ Y.left => g x) hs).trans
    ((congrArg (pullback.fst Y.hom a) hx).trans hy)

end Construction.Schemes

namespace Construction.Multiplication

/-- Finite multiplication is surjective on an arbitrary relative
abelian scheme, including all residue characteristics. -/
theorem surjective_power_of_isFinite
    {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (n : ℕ) [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] :
    Surjective ((𝟙 A : A ⟶ A) ^ n).left := by
  apply Schemes.surjective_of_algClosed_baseChanges
  intro K _ _ a
  let F := Over.pullback a
  let B := F.obj A
  have : Smooth B.hom := inferInstanceAs (Smooth (pullback.snd A.hom a))
  have : IsProper B.hom := inferInstanceAs (IsProper (pullback.snd A.hom a))
  have : GeometricallyConnected B.hom := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom a))
  have hp : F.map ((𝟙 A : A ⟶ A) ^ n) = (𝟙 B : B ⟶ B) ^ n :=
    ((F.homMonoidHom (X := A) (M := A)).map_pow (𝟙 A) n).trans
      (congrArg (fun q => q ^ n) (F.map_id A))
  have hfin : IsFinite (F.map ((𝟙 A : A ⟶ A) ^ n)).left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) a _ inferInstance
  have : IsFinite ((𝟙 B : B ⟶ B) ^ n).left := (congrArg (fun q => q.left) hp) ▸ hfin
  have hs : Surjective ((𝟙 B : B ⟶ B) ^ n).left := (MultiplicationFlat.Construction.Multiplication.surjective_flat_power_of_isFinite B n).1
  exact (congrArg (fun q => q.left) hp).symm ▸ hs

/-- Finite multiplication is an effective epimorphism in native schemes
over the base. This supplies the actual cover used for line descent. -/
theorem effectiveEpi_power_of_isFinite
    {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (n : ℕ) [IsFinite ((𝟙 A : A ⟶ A) ^ n).left] : EffectiveEpi ((𝟙 A : A ⟶ A) ^ n) := by
  have := MultiplicationFlat.Construction.Multiplication.flat_power_of_isFinite A n
  have := surjective_power_of_isFinite A n
  exact Picard.Homomorphisms.GroupDescent.Construction.effectiveEpi_over_of_fpqc ((𝟙 A : A ⟶ A) ^ n)

end Construction.Multiplication

namespace Construction.RelativeAbelian

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A)
  (ell : A ⟶ D.abelian) [IsMonHom ell] [IsFinite ell.left]

include D ell in
/-- Every positive multiplication map is finite, flat, surjective and
locally of finite presentation, without a global dimension parameter. -/
theorem positive_power_cover (n : ℕ) (hn : 0 < n) :
    IsFinite ((𝟙 A : A ⟶ A) ^ n).left ∧ Flat ((𝟙 A : A ⟶ A) ^ n).left ∧
      Surjective ((𝟙 A : A ⟶ A) ^ n).left ∧
        LocallyOfFinitePresentation ((𝟙 A : A ⟶ A) ^ n).left := by
  have hf := RelativeTorsion.Construction.RelativeAbelian.finite_positive_power A D ell n hn
  exact ⟨hf, MultiplicationFlat.Construction.Multiplication.flat_power_of_isFinite A n,
    Multiplication.surjective_power_of_isFinite A n,
    MultiplicationFlat.Construction.Multiplication.locallyOfFinitePresentation_overEnd A _⟩

end Construction.RelativeAbelian

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationCovers

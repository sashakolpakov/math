import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyCharacterEqualityOpen
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierCharacterRecoveryOpen

/-! # Family Cartier Recovery Open -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyCartierRecoveryOpen.Construction

noncomputable section

/-! The Cartier recovery open for a line on a parameter family lies
inside the product of that parameter with the original Cartier dual.
It covers the full parameter scheme, including its nilpotent structure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
  (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (T : Over S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback T.hom).obj B).left)
  (hL : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback T.hom).map f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.pullback T.hom).obj A).left)
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))

omit [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [Smooth B.hom] [GeometricallyConnected B.hom] in
def familyCartierRecoveryOpen : (T ⊗ C.dual.X).left.Opens :=
  FamilyCharacterEqualityOpen.Construction.familyCharacterEqualityOpen f T L hL (fst T C.dual.X)
    (C.sectionEquiv (T ⊗ C.dual.X) (snd T C.dual.X))

omit [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [Smooth B.hom] [GeometricallyConnected B.hom] in
theorem familyCartierRecoveryOpen_restrict_class {P : Over S} (b : P ⟶ T ⊗ C.dual.X)
    (hb : ∀ x : P.left, b.left x ∈ familyCartierRecoveryOpen f T L hL C) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B (b ≫ fst T C.dual.X))) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f P
        ((CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map b.op
          (C.sectionEquiv (T ⊗ C.dual.X) (snd T C.dual.X)))) :=
  FamilyCharacterEqualityOpen.Construction.familyCharacterEqualityOpen_restrict_class f T L hL (fst T C.dual.X)
    (C.sectionEquiv (T ⊗ C.dual.X) (snd T C.dual.X)) b hb

set_option backward.isDefEq.respectTransparency false in
theorem familyCartierRecoveryOpen_field_lift
    {k : Type u} [Field k] [CharZero k] (t : Spec (.of k) ⟶ S)
    (e : Over.mk t ⟶ T) (s : Spec (.of k)) :
    ∃ d : Over.mk t ⟶ T ⊗ C.dual.X,
      d ≫ fst T C.dual.X = e ∧ d.left s ∈ familyCartierRecoveryOpen f T L hL C := by
  have : IsIso (fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback (Over.mk t).hom).map f))
      ((Over.pullback (Over.mk t).hom).obj A)).left.appTop :=
    Geometric.ParameterCharacterRecovery.Construction.fieldParameterKernel_projection_appTop_isIso f t
  let L' := L.pullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B e)
  let hframe := Classical.choice (Quotient.exact (Parameter.LineComposition.Construction.parameterFamilyLine_pullback_trivial B f e L hL))
  obtain ⟨χ, hχ⟩ := Parameter.CharacterFrameRecovery.Construction.exists_parameterCharacter_of_pullback_frame f (Over.mk t) L' hframe
  let c := (C.sectionEquiv (Over.mk t)).symm χ
  let d := lift e c
  have hd : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map d.op
      (C.sectionEquiv (T ⊗ C.dual.X) (snd T C.dual.X)) = χ := by
    rw [← C.sectionEquiv_natural, show d ≫ snd T C.dual.X = c from lift_snd e c]
    exact (C.sectionEquiv (Over.mk t)).apply_symm_apply χ
  refine ⟨d, lift_fst e c, FamilyCharacterEqualityOpen.Construction.familyCharacterEqualityOpen_contains_field_character f T L hL
    (fst T C.dual.X) (C.sectionEquiv (T ⊗ C.dual.X) (snd T C.dual.X)) t d ?_ s⟩
  rw [hd, show d ≫ fst T C.dual.X = e from lift_fst e c]
  exact hχ

set_option backward.isDefEq.respectTransparency false in
theorem familyCartierRecoveryOpen_surjective
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k)) :
    Surjective ((familyCartierRecoveryOpen f T L hL C).ι ≫ (fst T C.dual.X).left) := by
  constructor
  intro x
  have : CharZero (T.left.residueField x) := CharZeroFieldParameters.Construction.residueField_charZero_of_map_to_field (T.hom ≫ p) x
  let s : Spec (T.left.residueField x) := ⟨⊥, inferInstance⟩
  let t := T.left.fromSpecResidueField x ≫ T.hom
  let e : Over.mk t ⟶ T := Over.homMk (T.left.fromSpecResidueField x) rfl
  obtain ⟨d, hd, hV⟩ := familyCartierRecoveryOpen_field_lift f T L hL C
    (k := T.left.residueField x) t e s
  refine ⟨⟨d.left s, hV⟩, ?_⟩
  change (fst T C.dual.X).left (d.left s) = x
  exact (congrArg (fun a : Over.mk t ⟶ T => a.left s) hd).trans
    (T.left.fromSpecResidueField_apply x s)

omit [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [Smooth B.hom] [GeometricallyConnected B.hom] in
theorem familyCartierRecoveryOpen_etale
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    Etale ((familyCartierRecoveryOpen f T L hL C).ι ≫ (fst T C.dual.X).left) := by
  have : Etale C.dual.X.hom := KilledGroupEtale.Construction.cartierRepresentative_etale_of_killed (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) C n
    (Relative.DegreeBaseChange.Construction.positiveNat_isUnit_on_charZero_field_scheme p n hn) hk
  have : Etale (fst T C.dual.X).left := inferInstanceAs (Etale (pullback.fst T.hom C.dual.X.hom))
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyCartierRecoveryOpen.Construction

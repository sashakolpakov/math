import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterEqualityOpen
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.ParameterCharacterRecovery
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CharZeroFieldParameters
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.KilledGroupEtale

/-! # Cartier Character Recovery Open -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierCharacterRecoveryOpen.Construction

noncomputable section

/-! The equality open inside the actual Cartier representative maps
surjectively to the base. It is an etale cover when an invertible
integer kills the original kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
  (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
  (hL : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left)
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))

omit [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [Smooth B.hom] [GeometricallyConnected B.hom] in
def cartierCharacterRecoveryOpen : C.dual.X.left.Opens :=
  Parameter.CharacterEqualityOpen.Construction.parameterCharacterEqualityOpen f L hL C.dual.X (C.sectionEquiv C.dual.X (𝟙 C.dual.X))

set_option backward.isDefEq.respectTransparency false in
theorem cartierCharacterRecoveryOpen_field_lift
    {k : Type u} [Field k] [CharZero k] (t : Spec (.of k) ⟶ S) (s : Spec (.of k)) :
    ∃ d : Over.mk t ⟶ C.dual.X, d.left s ∈ cartierCharacterRecoveryOpen f L hL C := by
  have : IsIso (CategoryTheory.CartesianMonoidalCategory.fst
      (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback (Over.mk t).hom).map f))
      ((Over.pullback (Over.mk t).hom).obj A)).left.appTop :=
    Geometric.ParameterCharacterRecovery.Construction.fieldParameterKernel_projection_appTop_isIso f t
  let L' := L.pullback (pullback.fst B.hom t)
  let e := Classical.choice (Quotient.exact (Parameter.LinePullbackKernel.Construction.originalLineParameter_pullback_trivial f L hL (Over.mk t)))
  obtain ⟨χ, hχ⟩ := Parameter.CharacterFrameRecovery.Construction.exists_parameterCharacter_of_pullback_frame f (Over.mk t) L' e
  let d := (C.sectionEquiv (Over.mk t)).symm χ
  have hd : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map d.op
      (C.sectionEquiv C.dual.X (𝟙 C.dual.X)) = χ := by
    rw [← C.sectionEquiv_natural, Category.comp_id]
    exact (C.sectionEquiv (Over.mk t)).apply_symm_apply χ
  refine ⟨d, Parameter.CharacterEqualityOpen.Construction.parameterCharacterEqualityOpen_contains_field_character f L hL C.dual.X
    (C.sectionEquiv C.dual.X (𝟙 C.dual.X)) t d ?_ s⟩
  rw [hd]
  exact hχ

set_option backward.isDefEq.respectTransparency false in
theorem cartierCharacterRecoveryOpen_surjective
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k)) :
    Surjective ((cartierCharacterRecoveryOpen f L hL C).ι ≫ C.dual.X.hom) := by
  constructor
  intro x
  have : CharZero (S.residueField x) := CharZeroFieldParameters.Construction.residueField_charZero_of_map_to_field p x
  let s : Spec (S.residueField x) := ⟨⊥, inferInstance⟩
  obtain ⟨d, hd⟩ := cartierCharacterRecoveryOpen_field_lift f L hL C
    (k := S.residueField x) (S.fromSpecResidueField x) s
  refine ⟨⟨d.left s, hd⟩, ?_⟩
  change C.dual.X.hom (d.left s) = x
  exact (congrArg (fun a : Spec (S.residueField x) ⟶ S => a s) d.w).trans
    (S.fromSpecResidueField_apply x s)

omit [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [Smooth B.hom] [GeometricallyConnected B.hom] in
theorem cartierCharacterRecoveryOpen_etale
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    Etale ((cartierCharacterRecoveryOpen f L hL C).ι ≫ C.dual.X.hom) := by
  have : Etale C.dual.X.hom := KilledGroupEtale.Construction.cartierRepresentative_etale_of_killed (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) C n
    (Relative.DegreeBaseChange.Construction.positiveNat_isUnit_on_charZero_field_scheme p n hn) hk
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierCharacterRecoveryOpen.Construction

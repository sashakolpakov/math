import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TotalParameters
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Markings

/-! # Intrinsic Family -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.IntrinsicFamily.Construction

noncomputable section

/-!
The universal quotient family with its actual integral action, full level,
and prescribed Lie signature. The parameter and full kernel model are
constructed from TorsionQuotient; the quotient is constructed from FiniteDescent. Polarization
and duality on the target are subsequent constructions, not premises here.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {D : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  {T : Over (Spec (.of K))}

/-- The native universal family and its verified structure. All quotient
objects and structure maps occur as existential conclusions. -/
def UniversalNativeFamily
    (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T) (n : ℕ)
    (M : Fin s → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)]
    [∀ i, Finite (M i)]
    (p q : Fin s → (A.polarized.abelian.scheme ⟶ A.polarized.abelian.scheme))
    [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (q i)]
    {W : Over T.left} [GrpObj W]
    (e : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i)) (B := OppositeKernel.Construction.torsionBlock n (q i)) (W := W)) :
    Prop :=
  ∃ Q : Over T.left, IsFinite Q.hom ∧ Etale Q.hom ∧
    ∃ repr : (Parameter.Products.Construction.blockTupleFunctor s (fun i =>
      SubgroupFunctor.Construction.supportedSubgroupFunctor A.polarized.abelian.scheme n (M i) (p i))).RepresentableBy Q,
    let F := ChoiceKernel.Construction.choiceFullKernel n s M p q e (Choices.Construction.universalBlockChoice n s M p repr)
    ∃ R : F.Model,
    let C := TotalParameters.Construction.totalParameter T Q
    let AC := PELBaseChange.Construction.pelObjectPullback A (TotalParameters.Construction.totalParameterSource T Q)
    ∃ (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) C.left)
      (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny AC.polarized.abelian B)
      (g : B.scheme ⟶ AC.polarized.abelian.scheme)
      (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B) (level : B.FullLevel N),
      Etale f.hom.left ∧ IsMonHom g ∧
      f.hom ≫ g = (𝟙 AC.polarized.abelian.scheme) ^ n ∧
      g ≫ f.hom = (𝟙 B.scheme) ^ n ∧
      (∀ a, f.hom ≫ σ.map a = AC.action.map a ≫ f.hom) ∧
      AbelianModuli.ReferenceFamily.PEL.Objects.HasPrescribedLieRanks D iota C B σ ∧
      (∀ (Y : Over C.left) (c : LocallyConstant Y.left (Multiplicative (Fin (2 * (3 * s)) → ZMod N))),
        (level.hom.app (.op Y) c).val = (AC.polarized.level.hom.app (.op Y) c).val ≫ f.hom) ∧
      (∀ (Y : Over C.left) (a : Y ⟶ AC.polarized.abelian.scheme),
        a ≫ f.hom = 1 ↔ ∃! h : Y ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
          h ≫ Intrinsic.Stability.Construction.nativeSubgroupInclusion A.polarized.abelian Q F R = a) ∧
      Descent.Construction.QuotientUniversalProperty (Intrinsic.Stability.Construction.nativeSubgroupInclusion A.polarized.abelian Q F R) f.hom

set_option backward.isDefEq.respectTransparency false in
/-- Construct the universal quotient with integral action, every ordered
full-level marking, and the prescribed signature from the complete TorsionQuotient
and FiniteDescent propositions and the split scalar-action equations. -/
theorem universal_native_family_from_TorsionQuotient_FiniteDescent
    [CharZero K] (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T) (n : ℕ) (hn : 0 < n)
    (hcop : Nat.Coprime n N)
    (M : Fin s → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)]
    [∀ i, Finite (M i)]
    (p q : Fin s → (A.polarized.abelian.scheme ⟶ A.polarized.abelian.scheme))
    [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (q i)]
    {W : Over T.left} [GrpObj W] [Etale W.hom] [IsSeparated W.hom]
    (e : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i)) (B := OppositeKernel.Construction.torsionBlock n (q i)) (W := W))
    (hsep : ∀ i j : ChoiceKernel.Construction.KernelIndex s, i ≠ j →
      Torsion.Groups.Construction.nativeTorsionMap n (ChoiceKernel.Construction.choiceKernelProjector s p q j) ≫
        Torsion.Groups.Construction.nativeTorsionMap n (ChoiceKernel.Construction.choiceKernelProjector s p q i) = 1)
    (scalar : NumberField.RingOfIntegers E → ChoiceKernel.Construction.KernelIndex s → ℤ)
    (hscalar : ∀ a i, OppositeKernel.Construction.torsionBlockInclusion n (ChoiceKernel.Construction.choiceKernelProjector s p q i) ≫ A.action.map a =
      (OppositeKernel.Construction.torsionBlockInclusion n (ChoiceKernel.Construction.choiceKernelProjector s p q i)) ^ scalar a i)
    (h_TorsionQuotient : Unit.Construction.TorsionQuotientInput.{0}) (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0}) :
    UniversalNativeFamily A n M p q e := by
  obtain ⟨Q, hQfinite, hQetale, ⟨repr⟩⟩ := Parameter.Products.Construction.chosen_block_parameters_from_TorsionQuotient
    T.hom A.polarized.abelian.scheme n hn s M p h_TorsionQuotient
  let U := Choices.Construction.universalBlockChoice n s M p repr
  let F := ChoiceKernel.Construction.choiceFullKernel n s M p q e U
  have htor := Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := A.polarized.abelian.scheme) T.hom n hn h_TorsionQuotient
  let R := ChoiceKernel.Construction.choiceFullKernel_model n s M p q e U hsep htor
  obtain ⟨B, f, g, hfetale, hg, hfg, hgf, hker, hUP⟩ :=
    Intrinsic.RelativeQuotient.Construction.native_relative_quotient_from_TorsionQuotient_FiniteDescent A.polarized.abelian Q F R n
      (ChoiceKernel.Construction.choiceFullKernel_killed n s M p q e U) htor.2 h_FiniteDescent
  obtain ⟨σ, hσ, _⟩ := Intrinsic.Action.Construction.native_quotient_integral_action A.polarized.abelian Q F R B f hker hUP
    A.action (fun a => BlockStability.Construction.choiceFullKernel_stable n s M p q e U
      (A.action.map a) (scalar a) (hscalar a))
  have : IsMonHom g := hg
  have : Etale f.hom.left := hfetale
  let C := TotalParameters.Construction.totalParameter T Q
  let AC := PELBaseChange.Construction.pelObjectPullback A (TotalParameters.Construction.totalParameterSource T Q)
  let level := Markings.Construction.transportFullLevel AC.polarized.abelian B f.hom g n N hcop hfg hgf AC.polarized.level
  refine ⟨Q, hQfinite, hQetale, repr, R, B, f, g, σ, level,
    hfetale, hg, hfg, hgf, hσ, ?_, ?_, hker, hUP⟩
  · exact Intrinsic.Action.Construction.prescribed_lie_ranks_after_quotient D iota C AC.polarized.abelian B AC.action σ
      f hσ AC.lieRanks
  · intro Y c
    exact Markings.Construction.transportFullLevel_apply AC.polarized.abelian B f.hom g n N hcop hfg hgf
      AC.polarized.level Y c

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.IntrinsicFamily.Construction

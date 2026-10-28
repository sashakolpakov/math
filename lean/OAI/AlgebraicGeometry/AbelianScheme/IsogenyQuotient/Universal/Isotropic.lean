import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.Isotropy
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicativeIntrinsicFamily
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsPerfectKernel

/-! # Isotropic -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.Isotropic.Construction

noncomputable section

/-!
The same finite etale parameter represents the original subgroup choices
and carries the actual quotient isogeny with self-annihilating kernel.
Its integral action, full ordered marking, and signature are constructed
together. The pairing on that source is the canonical base change of
the one supplied on the original family.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {D : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  {T : Over (Spec (.of K))}

/-- The complete native quotient construction with isotropy of its actual kernel.
All parameter, quotient, action, and marking data are existential conclusions. -/
def UniversalIsotropicNativeFamily
    (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T) (n : ℕ)
    (M : Fin s → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)]
    [∀ i, Finite (M i)]
    (p r : Fin s → (A.polarized.abelian.scheme ⟶ A.polarized.abelian.scheme))
    [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (r i)]
    (b : Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A.polarized.abelian.scheme n)
      (B := Torsion.Groups.Construction.nativeTorsionScheme A.polarized.abelian.scheme n)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T.left).X))
    (ep : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i)) (B := OppositeKernel.Construction.torsionBlock n (r i))
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T.left).X)) : Prop :=
    ∃ Q : Over T.left, IsFinite Q.hom ∧ Etale Q.hom ∧
      ∃ repr : (Parameter.Products.Construction.blockTupleFunctor s (fun i =>
        SubgroupFunctor.Construction.supportedSubgroupFunctor A.polarized.abelian.scheme n (M i) (p i))).RepresentableBy Q,
      let F := ChoiceKernel.Construction.choiceFullKernel n s M p r ep (Choices.Construction.universalBlockChoice n s M p repr)
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
          a ≫ f.hom = 1 ↔ ∃! z : Y ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
            z ≫ Intrinsic.Stability.Construction.nativeSubgroupInclusion A.polarized.abelian Q F R = a) ∧
        Descent.Construction.QuotientUniversalProperty (Intrinsic.Stability.Construction.nativeSubgroupInclusion A.polarized.abelian Q F R) f.hom ∧
        (let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion AC.polarized.abelian.scheme n)
          (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.hom)
         (Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback Q.hom (Grp.mk A.polarized.abelian.scheme)
           (Grp.mk A.polarized.abelian.scheme) n b).relativeAnnihilator H = H)

theorem universalNativeFamily_isotropic
    (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T) (n : ℕ)
    (M : Fin s → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)]
    [∀ i, Finite (M i)]
    (p r : Fin s → (A.polarized.abelian.scheme ⟶ A.polarized.abelian.scheme))
    [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (r i)]
    (b : Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A.polarized.abelian.scheme n)
      (B := Torsion.Groups.Construction.nativeTorsionScheme A.polarized.abelian.scheme n)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T.left).X))
    (ep : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i)) (B := OppositeKernel.Construction.torsionBlock n (r i))
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T.left).X))
    (hu : IntrinsicFamily.Construction.UniversalNativeFamily A n M p r ep)
    (hisotropic : ∀ (Q : Over T.left)
      (U : ∀ i, SubgroupFunctor.Construction.SupportedChoice A.polarized.abelian.scheme n (M i) (p i) Q),
      let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A.polarized.abelian.scheme n)
        (ChoiceKernel.Construction.choiceFullKernel n s M p r ep U)
      b.relativeAnnihilator H = H) :
    UniversalIsotropicNativeFamily A n M p r b ep := by
  obtain ⟨Q, hQf, hQe, repr, R, B, f, g, σ, level,
    hf, hg, hfg, hgf, hσ, hranks, hlevel, hker, hUP⟩ := hu
  refine ⟨Q, hQf, hQe, repr, R, B, f, g, σ, level,
    hf, hg, hfg, hgf, hσ, hranks, hlevel, hker, hUP, ?_⟩
  exact Intrinsic.Isotropy.Construction.nativeQuotient_kernel_self_annihilating A.polarized.abelian Q _ R f hker n b
    (hisotropic Q (Choices.Construction.universalBlockChoice n s M p repr))

theorem universal_isotropic_native_quotient
    {E K L : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] [CharZero K] [Field L] [NumberField L] {κ : L →+* ℂ}
    {s N : ℕ} {D : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T)
    (q : ℕ) [Fact q.Prime] (hcop : Nat.Coprime q N) (h : ℕ)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (arithmeticEmbedding : E →+* L)
    (hsplit : j.HasSplitCoordinates arithmeticEmbedding) (labels : ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))
    (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
    (M : Fin s → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module (ZMod (q ^ h)) (M i)] [∀ i, Finite (M i)]
    (b : Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A.polarized.abelian.scheme (q ^ h))
      (B := Torsion.Groups.Construction.nativeTorsionScheme A.polarized.abelian.scheme (q ^ h))
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T.left).X))
    (hb : b.toSheafPairing.IsPerfect)
    (halt : ∀ (X : Over T.left) (x : X ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.polarized.abelian.scheme (q ^ h)),
      b.pairValue x x = 1)
    (hOE : ∀ (a : NumberField.RingOfIntegers E) (X : Over T.left)
      (x y : X ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.polarized.abelian.scheme (q ^ h)),
      b.pairValue (x ≫ Torsion.Groups.Construction.nativeTorsionMap (q ^ h) (A.action.map a)) y =
        b.pairValue x (y ≫ Torsion.Groups.Construction.nativeTorsionMap (q ^ h)
          (A.action.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))))
    (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0}) :
    let p := CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h s labels
    let r := CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h s labels
    let ep := CM.PointsPerfectKernel.Construction.l45SourceBlockPairing j arithmeticEmbedding hsplit A.polarized.abelian A.action h s labels b
    UniversalIsotropicNativeFamily A (q ^ h) M p r b ep := by
  let p := CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h s labels
  let r := CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h s labels
  let ep := CM.PointsPerfectKernel.Construction.l45SourceBlockPairing j arithmeticEmbedding hsplit A.polarized.abelian A.action h s labels b
  have hu : IntrinsicFamily.Construction.UniversalNativeFamily A (q ^ h) M p r ep := by
    apply MultiplicativeIntrinsicFamily.Construction.universal_multiplicative_native_family_from_TorsionQuotient_FiniteDescent A (q ^ h)
      (pow_pos (Fact.out : q.Prime).pos h) (hcop.pow_left h) M p r ep
      (scalar := fun a i => ((j.residueCharacter arithmeticEmbedding (labels i) h a).val : ℤ))
      (h_TorsionQuotient := Torsion.Construction.verified_TorsionQuotientInput) (h_FiniteDescent := h_FiniteDescent)
    · intro i k hik
      exact CM.PointsChoiceIsotropy.Construction.l45_choice_torsion_orthogonal j arithmeticEmbedding hsplit A.polarized.abelian
        A.action h s labels k i hik.symm
    · intro a i
      have hc := CM.PointsProjectorSum.Construction.l45_native_projector_scalar j arithmeticEmbedding hsplit A.polarized.abelian
        A.action h (labels i) a
      cases i <;> exact hc
  apply universalNativeFamily_isotropic A (q ^ h) M p r b ep hu
  intro Q U
  exact CM.PointsPerfectKernel.Construction.l45_choice_kernel_self_annihilating_from_perfect_source j arithmeticEmbedding hsplit
    A.polarized.abelian A.action h s labels b T.hom hlabels M U hb halt hOE

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.Isotropic.Construction

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.TranslationKernelFinite
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.EtaleGroup

/-! # Translation Quotient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.TranslationQuotient

noncomputable section

/-! The quotient by the full ample translation kernel exists as an
abelian scheme of the original dimension. Its kernel and quotient
universal property hold on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.EtaleGroup.Construction

variable {S : Scheme} [IsLocallyNoetherian S] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)

local instance ampleTranslationSource_locallyNoetherian : IsLocallyNoetherian A.scheme.left :=
  LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom

structure AmpleTranslationQuotient where
  exponent : ℕ
  exponent_pos : 0 < exponent
  target : Abelian.Schemes.AbelianScheme g S
  isogeny : Abelian.Schemes.AbelianScheme.Isogeny A target
  complementary : target.scheme ⟶ A.scheme
  etale : Etale isogeny.hom.left
  complementary_monHom : IsMonHom complementary
  source_multiple : isogeny.hom ≫ complementary = (𝟙 A.scheme) ^ exponent
  target_multiple : complementary ≫ isogeny.hom = (𝟙 target.scheme) ^ exponent
  kernel : ∀ (T : Over S) (a : T ⟶ A.scheme), a ≫ isogeny.hom = 1 ↔
    ∃! z : T ⟶ Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P, z ≫ Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P = a
  universal : AbelianScheme.IsogenyQuotient.Descent.Construction.QuotientUniversalProperty (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P) isogeny.hom

theorem ampleTranslationQuotient_nonempty [IsAffine S]
    (qS : S ⟶ Spec (.of ℚ)) (hL : L.IsAmple) :
    Nonempty (AmpleTranslationQuotient A L P) := by
  let Z := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P
  let i := Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P
  let : GrpObj Z := (Picard.ThetaConstruction.RelativeDifferenceGroup.Geometric.relativeDifferenceZeroGroup A L P).group
  let : IsCommMonObj Z := Picard.ThetaConstruction.RelativeDifferenceGroup.Geometric.relativeDifferenceZeroGroup_commutative A L P
  let : IsMonHom i := Picard.ThetaConstruction.RelativeDifferenceGroup.Geometric.relativeDifferenceZeroInclusion_isMonHom A L P
  let : IsFinite Z.hom := Rational.TranslationKernelFinite.rationalTranslationKernel_isFinite qS A L P hL
  let : Etale Z.hom := Rational.TranslationKernelEtale.rationalTranslationKernel_etale qS A L P hL
  obtain ⟨n, hn, hkill⟩ := Rational.TranslationKernelFinite.rationalTranslationKernel_exists_exponent qS A L P hL
  have hi : i ^ n = 1 := by
    have h := congrArg (fun b => b ≫ i) hkill
    simpa only [MonObj.pow_comp, MonObj.one_comp, Category.id_comp] using h
  obtain ⟨B, f, r, he, hr, hfr, hrf, hk, hu⟩ := AbelianScheme.IsogenyQuotient.Finite.EtaleGroup.Construction.finiteEtaleGroupQuotient_exists A Z i
    (Rational.TranslationKernelFinite.rationalTranslationKernel_inclusion_closedImmersion qS A L P hL) n hi
  exact ⟨⟨n, hn, B, f, r, he, hr, hfr, hrf, hk, hu⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.TranslationQuotient

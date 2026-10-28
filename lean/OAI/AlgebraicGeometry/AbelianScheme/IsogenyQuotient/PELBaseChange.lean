import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.Action
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange

/-! # PEL Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELBaseChange.Construction

noncomputable section

/-!
Base change of the actual ReferenceFamily PEL data. The Poincare characterization
of Rosati and every geometric Lie rank are proved to persist; they are
not supplied again as conditions on the pulled-back universal family.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v

set_option backward.isDefEq.respectTransparency false in
theorem poincareClass_pullback_pair
    {S S' : Scheme.{u}} {dim : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme dim S}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (a : D.abelian.scheme ⟶ D.abelian.scheme) (b : A.scheme ⟶ A.scheme) (f : S' ⟶ S) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback f).map a ⊗ₘ (Over.pullback f).map b).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.pullback f).poincare) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (D.poincarePullbackOverMap f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (a ⊗ₘ b).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)) := by
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp
    ((Over.pullback f).map a ⊗ₘ (Over.pullback f).map b).left
    (D.poincarePullbackOverMap f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)).symm.trans
      ((congrArg (fun z => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass z (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
        (AbelianModuli.HilbertConstruction.Moduli.BaseChange.poincarePullbackOverMap_naturality D D a b f)).trans
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (D.poincarePullbackOverMap f).left
            (a ⊗ₘ b).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)))

set_option backward.isDefEq.respectTransparency false in
/-- The dual Poincare characterization and the Rosati equation survive
an arbitrary base change of the polarized family. -/
theorem rosatiConjugation_pullback
    {S S' : Scheme.{u}} {dim N : ℕ} {δ : Fin dim → ℕ}
    {E : Type v} [Field E] [NumberField E] [NumberField.IsCMField E]
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel dim δ N S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (f : S' ⟶ S) :
    AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback f) (ρ.pullback f) := by
  intro a
  obtain ⟨ad, had, hchar, hrel⟩ := hρ a
  have : IsMonHom ad := had
  refine ⟨(Over.pullback f).map ad, inferInstance, ?_, ?_⟩
  · have hleft := poincareClass_pullback_pair A.dual ad (𝟙 A.abelian.scheme) f
    have hright := poincareClass_pullback_pair A.dual (𝟙 A.dual.abelian.scheme) (ρ.map a) f
    have hmiddle := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.dual.poincarePullbackOverMap f).left)
      hchar
    have h := hleft.trans (hmiddle.trans hright.symm)
    have hL := congrArg (fun b : (A.abelian.pullback f).scheme ⟶ (A.abelian.pullback f).scheme =>
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback f).map ad ⊗ₘ b).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (A.dual.pullback f).poincare))
      ((Over.pullback f).map_id A.abelian.scheme)
    have hR := congrArg (fun b : (A.dual.abelian.pullback f).scheme ⟶
        (A.dual.abelian.pullback f).scheme =>
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (b ⊗ₘ (Over.pullback f).map (ρ.map a)).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (A.dual.pullback f).poincare))
      ((Over.pullback f).map_id A.dual.abelian.scheme)
    exact hL.symm.trans (h.trans hR)
  · change (Over.pullback f).map A.polarization.isogeny.hom ≫ (Over.pullback f).map ad =
      (Over.pullback f).map (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a)) ≫
        (Over.pullback f).map A.polarization.isogeny.hom
    simpa only [← Functor.map_comp] using congrArg (Over.pullback f).map hrel

set_option backward.isDefEq.respectTransparency false in
/-- Pulling the source family back preserves the prescribed signature,
using the actual comparison of iterated and composite geometric fibers. -/
theorem prescribed_lie_ranks_pullback
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (iota : E →+* K)
    {T U : Over (Spec (.of K))} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) T.left)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (hrank : AbelianModuli.ReferenceFamily.PEL.Objects.HasPrescribedLieRanks P iota T A ρ) (f : U ⟶ T) :
    AbelianModuli.ReferenceFamily.PEL.Objects.HasPrescribedLieRanks P iota U (A.pullback f.left) (ρ.pullback f.left) := by
  intro F _ _ j p hp τ
  have hbase : (p ≫ f.left) ≫ T.hom = Spec.map (CommRingCat.ofHom j) := by
    rw [Category.assoc, f.w]
    exact hp
  have hr := hrank F j (p ≫ f.left) hbase τ
  let e := A.pullbackCompIso f.left p
  have : IsIso e.hom.left := (Over.forget (Spec (.of F))).map_isIso e.hom
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom (A.pullbackCompIso f.left p).hom)
  apply LieRank.Construction.hasLieRank_of_finite_etale (A.pullback (p ≫ f.left)) ((A.pullback f.left).pullback p)
    e.hom (ρ.pullback (p ≫ f.left)) ((ρ.pullback f.left).pullback p) _ _ (P.lieRank τ) hr
  intro a
  change e.hom ≫ (Over.pullback p).map ((Over.pullback f.left).map (ρ.map a)) =
    (Over.pullback (p ≫ f.left)).map (ρ.map a) ≫ e.hom
  dsimp only [e]
  rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_hom]
  exact ((Over.pullbackComp p f.left).hom.naturality (ρ.map a)).symm

/-- The entire source PEL object is pulled back with its proved Rosati
and signature conditions, in addition to polarization and full level. -/
def pelObjectPullback
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T U : Over (Spec (.of K))} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T) (f : U ⟶ T) :
    AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N U where
  polarized := A.polarized.pullback f.left
  action := A.action.pullback f.left
  rosati := rosatiConjugation_pullback A.polarized A.action A.rosati f.left
  lieRanks := prescribed_lie_ranks_pullback P iota A.polarized.abelian A.action A.lieRanks f

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELBaseChange.Construction

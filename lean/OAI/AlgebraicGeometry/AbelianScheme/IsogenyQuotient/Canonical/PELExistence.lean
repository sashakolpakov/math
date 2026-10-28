import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PolarizationExistence
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.FamilyRosati
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELBaseChange

/-! # PEL Existence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PELExistence.Construction

noncomputable section

/-! The canonical geometric quotient has the full positive polarized
PEL structure, including its original Poincare Rosati and Lie-rank
predicates. The dual and polarization are constructed from isotropy. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

def polarizedQuotientData {S : Scheme} {g N : ℕ} {δ : Fin g → ℕ}
    (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (p : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ) (level : B.FullLevel N) :
    AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S where
  abelian := B
  dual := DB
  polarization := p
  level := level

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {d N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T)
  (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ T.left)
  (n : ℕ) (hn : 0 < n) {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * d) (Spec (.of k))}
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.polarized.abelian.pullback s) B) [Etale f.hom.left]
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B) (level : B.FullLevel N)
  (hσ : ∀ a, (A.action.pullback s).map a ≫ f.hom = f.hom ≫ σ.map a)
  (hker : ∀ (U : Over (Spec (.of k))) (x : U ⟶ (A.polarized.abelian.pullback s).scheme),
    x ≫ f.hom = 1 → x ^ n = 1)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.polarized.abelian.pullback s).scheme n)
      (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.hom)
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.polarized.abelian.pullback s) (A.polarized.dual.pullback s)
      (A.polarized.polarization.pullback s) n hn).relativeAnnihilator F = F)

include hσ hker hlag in
set_option backward.isDefEq.respectTransparency false in
theorem geometricCanonicalQuotient_full_pel_exists
    (hc : Nat.Coprime n ((∏ j, P.polarizationType j) ^ 2)) :
    ∃ (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) (p : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB P.polarizationType),
      AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (polarizedQuotientData B DB p level) σ ∧
      AbelianModuli.ReferenceFamily.PEL.Objects.HasPrescribedLieRanks P iota (Over.mk (s ≫ T.hom)) B σ ∧
      f.hom ≫ p.isogeny.hom ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom
        (A.polarized.dual.pullback s) DB =
          (Geometric.PoincareSymmetry.Construction.geometricPolarizationMap A.polarized.dual A.polarized.polarization k s) ^ n := by
  obtain ⟨DB, p, hp⟩ := PolarizationExistence.Construction.geometricCanonicalQuotient_polarization_exists
    A.polarized.dual A.polarized.polarization k s n hn f hker hlag hc
  let u : Over.mk (s ≫ T.hom) ⟶ T := Over.homMk s
  let AS := PELBaseChange.Construction.pelObjectPullback A u
  let F := TateComparison.PEL.PELFamilyData.ofPolarized AS.polarized (TateComparison.PELAdapters.actionToEnd AS.action)
  have hact : ∀ a, (TateComparison.PELAdapters.actionFromEnd F.action).map a ≫ f.hom = f.hom ≫ σ.map a := by
    intro a
    exact (congrArg (fun b => b ≫ f.hom) (TateComparison.PELAdapters.actionToEnd_schemeMap AS.action a)).trans (hσ a)
  have hR := Picard.FamilyRosati.Construction.picardQuotientFamily_rosati F B DB p.isogeny σ level f n hact hp
    (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom
    ((TateComparison.PELAdapters.rosati_iff AS.polarized AS.action).mpr AS.rosati)
  refine ⟨DB, p, (TateComparison.PELAdapters.rosati_iff (polarizedQuotientData B DB p level) σ).mp hR, ?_, hp⟩
  exact Intrinsic.Action.Construction.prescribed_lie_ranks_after_quotient P iota (Over.mk (s ≫ T.hom))
    AS.polarized.abelian B AS.action σ f (fun a => (hσ a).symm) AS.lieRanks

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PELExistence.Construction

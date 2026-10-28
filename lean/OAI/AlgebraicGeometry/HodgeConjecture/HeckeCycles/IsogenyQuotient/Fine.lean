import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.PEL
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELUniversalFunctions
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TotalParameters
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotient

/-! # Fine -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.Fine.CM.Isogeny

noncomputable section

/-! Retain the native IsogenyQuotient cover and target, and express their actual
universal isogeny in TateComparison's family conventions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s N n : ℕ} [NeZero N]
  {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)
  (κ : K →+* ℂ) (hC : M.HasProjectiveBallComponents κ)
  (Q : Over M.space.left) (hQf : IsFinite Q.hom) (hQe : Etale Q.hom)
  (f : AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData.Construction.NativeFinePELTarget (M.universal.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q)) n M)

abbrev family := PELFamily.CM.Family.ofActionData (PELModuli.IntegralModel.PEL.Has.characteristicZeroPELData P M.universal)

def correspondence : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.space where
  cover := AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter M.space Q
  source := AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q
  target := f.target
  finite := hQf
  etale := hQe

def isogeny : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny ((family M).pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q).left)
    ((family M).pullback f.target.left) n := by
  let A := (PELModuli.IntegralModel.PEL.Has.characteristicZeroPELData P M.universal).pullback
    (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q).left
  let B := (PELModuli.IntegralModel.PEL.Has.characteristicZeroPELData P M.universal).pullback f.target.left
  let g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.polarized.abelian B.polarized.abelian := f.isogeny
  have hA : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions A.polarized.abelian.scheme :=
    (AbelianScheme.IsogenyQuotient.FinePELUniversalFunctions.Construction.finePEL_universal_hasUniversalGlobalFunctions M hM κ hC).pullback
      (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q).left
  have hB : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions B.polarized.abelian.scheme :=
    AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source g.hom hA
  exact PEL.CM.Isogeny.isogeny A B hA hB g f.polarization
    (fun a => (f.action a).symm) f.marking

theorem isogeny_hom : (Isogeny.isogeny M hM κ hC Q f).isogeny.hom = f.isogeny.hom := by
  rfl

include hM hC in
theorem polarization_unique
    (p : (M.universal.polarized.abelian.pullback f.target.left).scheme ⟶
      (M.universal.polarized.dual.abelian.pullback f.target.left).scheme)
    [IsMonHom p]
    (hp : f.isogeny.hom ≫ p ≫ AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.isogeny.hom
      (M.universal.polarized.dual.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q).left)
      (M.universal.polarized.dual.pullback f.target.left) =
        (M.universal.polarized.polarization.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q).left).isogeny.hom ^ n) :
    p = (M.universal.polarized.polarization.pullback f.target.left).isogeny.hom := by
  let A := (PELModuli.IntegralModel.PEL.Has.characteristicZeroPELData P M.universal).pullback
    (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q).left
  let B := (PELModuli.IntegralModel.PEL.Has.characteristicZeroPELData P M.universal).pullback f.target.left
  have hA : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions A.polarized.abelian.scheme :=
    (AbelianScheme.IsogenyQuotient.FinePELUniversalFunctions.Construction.finePEL_universal_hasUniversalGlobalFunctions M hM κ hC).pullback
      (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M.space Q).left
  let g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.polarized.abelian B.polarized.abelian := f.isogeny
  have hB : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions B.polarized.abelian.scheme :=
    AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source g.hom hA
  let p' : B.polarized.abelian.scheme ⟶ B.polarized.dual.abelian.scheme := p
  let : IsMonHom p' := inferInstanceAs (IsMonHom p)
  exact PEL.CM.Isogeny.polarization_unique A B hB g f.polarization p' hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.Fine.CM.Isogeny

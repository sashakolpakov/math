import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.RelativePairing
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.DoubleAnnihilator

/-! # Relative Annihilator -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.RelativeAnnihilator.Construction

noncomputable section

/-!
The canonical polarization pairing determines the original relative
subgroup by double annihilation. Its perfection and finite locally free
torsion geometry are derived from the actual polarization. The parameter
scheme and every test scheme are unrestricted.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {A : CartierDuality.PolarizedTorsion.AbelianScheme S}
  (pol : CartierDuality.PolarizedTorsion.Polarization A) (n : ℕ) (hn : 0 < n)
  (hdegree : ∀ s : S, Nat.Coprime n (pol.fiberDegree s))

include hdegree

theorem canonicalPolarization_relative_double_annihilator
    (P : Over S) (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup (Torsion.Groups.Construction.nativeTorsionScheme A.toOver n) P) (R : F.Model) :
    let e := RelativePairing.Construction.canonicalNativePolarizationPairing pol n hn
    e.flip.relativeAnnihilator (e.relativeAnnihilator F) = F := by
  have h := RelativePairing.Construction.canonicalNativeTorsion_finiteLocallyFree pol n hn
  have : IsFinite (Torsion.Groups.Construction.nativeTorsionScheme A.toOver n).hom := h.1
  have : Flat (Torsion.Groups.Construction.nativeTorsionScheme A.toOver n).hom := h.2.1
  have : LocallyOfFinitePresentation (Torsion.Groups.Construction.nativeTorsionScheme A.toOver n).hom := h.2.2
  exact Relative.DoubleAnnihilator.Construction.relative_double_annihilator_from_perfect_pairing
    (Grp.mk (Torsion.Groups.Construction.nativeTorsionScheme A.toOver n)) (Grp.mk (Torsion.Groups.Construction.nativeTorsionScheme A.toOver n))
    P F R (RelativePairing.Construction.canonicalNativePolarizationPairing pol n hn)
    (RelativePairing.Construction.canonicalNativePolarizationPairing_isPerfect pol n hn hdegree)

theorem canonicalPolarization_parameter_annihilator
    (P : Over S) (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup (Torsion.Groups.Construction.nativeTorsionScheme A.toOver n) P) (R : F.Model) :
    let G := Grp.mk (Torsion.Groups.Construction.nativeTorsionScheme A.toOver n)
    let eP := PairingBaseChange.Construction.nativePairingPullback P.hom G G (RelativePairing.Construction.canonicalNativePolarizationPairing pol n hn)
    let FP := Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F
    Nonempty (eP.relativeAnnihilator FP).Model ∧
      eP.flip.relativeAnnihilator (eP.relativeAnnihilator FP) = FP := by
  have h := RelativePairing.Construction.canonicalNativeTorsion_finiteLocallyFree pol n hn
  have : IsFinite (Torsion.Groups.Construction.nativeTorsionScheme A.toOver n).hom := h.1
  have : Flat (Torsion.Groups.Construction.nativeTorsionScheme A.toOver n).hom := h.2.1
  have : LocallyOfFinitePresentation (Torsion.Groups.Construction.nativeTorsionScheme A.toOver n).hom := h.2.2
  exact Parameter.Annihilator.Construction.relativeParameter_annihilator_from_perfect_pairing
    (Grp.mk (Torsion.Groups.Construction.nativeTorsionScheme A.toOver n)) (Grp.mk (Torsion.Groups.Construction.nativeTorsionScheme A.toOver n))
    P F R (RelativePairing.Construction.canonicalNativePolarizationPairing pol n hn)
    (RelativePairing.Construction.canonicalNativePolarizationPairing_isPerfect pol n hn hdegree)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.RelativeAnnihilator.Construction

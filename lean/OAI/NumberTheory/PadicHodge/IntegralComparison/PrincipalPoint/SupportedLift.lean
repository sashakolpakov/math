import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.SupportedTransfer
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Fraction

/-! # Supported Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.SupportedLift

noncomputable section

/-! The native augmented point resolution admits an explicit lift to
the genuine supported principal Čech total. Its original oriented
residue sends this lift to the normalized surviving point class. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) [IsClosedImmersion g]
  (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))
  (K : ChainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj (Principal.ClosedQuotient.directImage g))
  [QuasiIso ε] [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  {c m : ℕ} (s : Fin c → Γ(Y, U)) (t : Fin m → Γ(Y, U))
  (hst : Koszul.OrientedTopCohomology.ideal Γ(Y, U) (Fin.append s t) =
    g.ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn (Fin.append s t)))

local instance point_quasicoherent : (Principal.ClosedQuotient.directImage g).IsQuasicoherent := by
  let : (SheafOfModules.unit Z.ringCatSheaf).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  exact AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom g

abbrev equivalence := Principal.Koszul.Comparison.equivalence U hU N e K
  (Principal.ClosedQuotient.directImage g) ε (Fin.append s t) hreg
    (Principal.OrientedResidue.quotientIso g U hU (Fin.append s t) hst)

abbrev lift := KoszulPoint.SupportedTransfer.lift Γ(Y, U) (Principal.SectionPresheaf.rings U hU)
  (Fraction.family U t) s t (Fraction.units U hU t)
    (equivalence g U hU N e K ε s t hst hreg)

abbrev forget := KoszulPoint.SupportedTransfer.forget Γ(Y, U) (Principal.SectionPresheaf.rings U hU)
  (Fraction.family U t) s t (Fraction.units U hU t)
    (equivalence g U hU N e K ε s t hst hreg)

abbrev residue (q : ℕ) := KoszulPoint.SupportedTransfer.residue Γ(Y, U) (Principal.SectionPresheaf.rings U hU)
  (Fraction.family U t) s t (Fraction.units U hU t)
    (equivalence g U hU N e K ε s t hst hreg)
      (Principal.ClosedKoszulResidue.residue g U hU (Fin.append s t) hst) q

abbrev residue_forget (q : ℕ) := KoszulPoint.SupportedTransfer.residue_forget
  Γ(Y, U) (Principal.SectionPresheaf.rings U hU) (Fraction.family U t) s t
    (Fraction.units U hU t) (equivalence g U hU N e K ε s t hst hreg)
      (Principal.ClosedKoszulResidue.residue g U hU (Fin.append s t) hst) q

theorem residue_map : (equivalence g U hU N e K ε s t hst hreg).hom ≫
    Principal.ClosedKoszulResidue.residue g U hU (Fin.append s t) hst =
      Principal.OrientedResidue.map g U hU N e K ε (Fin.append s t) hst hreg := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.SupportedLift

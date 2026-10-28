import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ComplexPELRigidity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.PELAdapter

/-! # Complex Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.ComplexRigidity

noncomputable section

/-! Pure polarized full-level automorphisms are trivial over the actual
complex base. The homology isometry follows from the given polarization
and Poincare equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

theorem pureComplex_abelian_eq_id (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A A) (hN : 3 ≤ N) :
    e.abelian.hom = 𝟙 A.abelian.scheme := by
  apply AbelianScheme.TateComparison.ComplexPELRigidity.polarized_abelian_eq_id A e.abelian hN _ e.level
  intro x y
  let B := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  have h := Product.ClassPairingNaturality.nativeProductClassPairing_pullback B B B B e.abelian.hom e.abelian.hom
    (Polarization.Adjoints.polarizationBiextensionClass A) x y
  change Product.ClassPairingNaturality.nativeProductClassPairing B B (Polarization.Adjoints.polarizationBiextensionClass A) _ _ =
    1 • Product.ClassPairingNaturality.nativeProductClassPairing B B (Polarization.Adjoints.polarizationBiextensionClass A) x y
  rw [one_nsmul]
  exact h.symm.trans (congrArg (fun c => Product.ClassPairingNaturality.nativeProductClassPairing B B c x y)
    (Polarization.Adjoints.polarizationBiextensionClass_iso A A e))

theorem purePELComplex_abelian_eq_id
    (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso (PELAdapter.pureAsPEL A) (PELAdapter.pureAsPEL A)) (hN : 3 ≤ N) :
    e.abelian.hom = 𝟙 A.abelian.scheme :=
  pureComplex_abelian_eq_id A (PELAdapter.pureIsoOfPEL e) hN

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.ComplexRigidity

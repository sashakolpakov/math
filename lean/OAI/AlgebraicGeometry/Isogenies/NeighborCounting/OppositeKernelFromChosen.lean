import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.KernelOrthogonal
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.PairingProjectors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf

/-! # Opposite Kernel From Chosen -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OppositeKernelFromChosen

noncomputable section

/-! An opposite component of the actual polarized isogeny kernel is
determined by the chosen component. This is derived from character
descent, the original Rosati adjoints, and actual O_E-equivariance. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.KernelOrthogonal.ReferenceSheafPoints OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.KernelOrthogonal OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.PairingProjectors
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Opposite

variable {k : Type} [Field k] [IsAlgClosed k] {g h N M : ℕ} {δ : Fin g → ℕ} {ε : Fin h → ℕ}
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (PA : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (PB : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel h ε M (Spec (.of k)))
variable (ρA : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PA.abelian)
variable (ρB : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PB.abelian)
variable (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation PA ρA)
variable (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny PA.abelian PB.abelian)
variable (hfρ : ∀ a, ρA.map a ≫ f.hom = f.hom ≫ ρB.map a)
variable (n : ℕ)
variable (hk : ∀ (T : Over (Spec (.of k))) (a : T ⟶ PA.abelian.scheme), a ≫ f.hom = 1 → a ^ (q ^ n) = 1)
variable (hpol : AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f.hom PA.dual PB.dual PB.polarization = PA.polarization.isogeny.hom ^ (q ^ n))
variable (hdegree : q.Coprime (∏ i, ε i))

include hρ hfρ hk hpol hdegree in
theorem opposite_kernel_iff_chosen_orthogonal (τ υ : Gal(E/ℚ))
    (hυ : υ = PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ)
    (T : Over (Spec (.of k))) (x : (PA.abelian.torsionFunctor (q ^ n)).obj (.op T))
    (hx : x.val ≫ ρA.map (j.projector iota hsplit n υ) = x.val) :
    x.val ≫ f.hom = 1 ↔
      ∀ (U : Over (Spec (.of k))) (t : U ⟶ T)
        (y : (PA.abelian.torsionFunctor (q ^ n)).obj (.op U)),
        y.val ≫ f.hom = 1 → y.val ≫ ρA.map (j.projector iota hsplit n τ) = y.val →
        AbelianScheme.FrobeniusKernel.Prescription.Construction.canonicalTorsionOrthogonal PA (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U y
          ((PA.abelian.torsionFunctor (q ^ n)).map t.op x) := by
  have hann := Reference.KernelOrthogonal.polarized_original_kernel_orthogonal_iff PA PB f (q ^ n)
    (pow_pos (Fact.out : q.Prime).pos n) hk ρA hρ hpol (hdegree.pow_left n) T x
  constructor
  · intro hkill U t y hy _
    obtain ⟨z, hz, _⟩ := (Picard.Homomorphisms.Kernel.Construction.kernelScheme_universal f.hom U y.val).mp hy
    have hzy : Reference.KernelOrthogonal.ReferenceSheafPoints.originalKernelTorsionPoint PA PB f (q ^ n) hk U z = y := Subtype.ext hz
    exact hzy ▸ (hann.mpr hkill U t z)
  · intro htest
    apply hann.mp
    intro U t z
    let y := Reference.KernelOrthogonal.ReferenceSheafPoints.originalKernelTorsionPoint PA PB f (q ^ n) hk U z
    let py := AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit PA ρA n τ U y
    have hpy : py.val ≫ f.hom = 1 := by
      change (y.val ≫ ρA.map (j.projector iota hsplit n τ)) ≫ f.hom = 1
      rw [Category.assoc, hfρ, ← Category.assoc]
      rw [show y.val ≫ f.hom = 1 from Reference.KernelOrthogonal.ReferenceSheafPoints.originalKernelPoint_killed PA PB f U z, MonObj.one_comp]
    have hfixed : py.val ≫ ρA.map (j.projector iota hsplit n τ) = py.val :=
      PELModuli.CMPoints.BlockDecomposition.projector_idempotent_on_torsion j iota hsplit PA.abelian ρA n τ U y.val y.property
    have h := (Reference.PairingProjectors.canonicalTorsionOrthogonal_projectors j iota hsplit PA ρA n τ hρ υ hυ U y
      ((PA.abelian.torsionFunctor (q ^ n)).map t.op x)).mp (htest U t py hpy hfixed)
    have hp := PrescribedKernelOf.Opposite.prescribed_component_fixed j iota hsplit PA ρA n υ U
      ((PA.abelian.torsionFunctor (q ^ n)).map t.op x)
      (PrescribedKernelOf.Opposite.prescribed_support_natural j iota hsplit PA ρA n υ t x hx)
    exact hp ▸ h

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OppositeKernelFromChosen

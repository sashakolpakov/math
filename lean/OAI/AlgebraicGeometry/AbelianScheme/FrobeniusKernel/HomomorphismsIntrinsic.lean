import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Quotient
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Theorem

/-! # Homomorphisms Intrinsic -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HomomorphismsIntrinsic.Construction

noncomputable section

/-! Homomorphisms at ddba648bd04271074ed5478a97d886250372350c is a proved
native input. Apply all five conclusions to the original polarized
source, and identify its independently constructed sheaf quotient.
No Frobenius or polarization conclusion is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k q]
variable {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)

/-- Every native Homomorphisms conclusion applies to the original fixed-field
source. The ordinary hypothesis is only its geometric torsion count. -/
theorem e57NativeSourceConclusions :
    let hS := Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)
    let F := Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q Fact.out hS A.scheme
    Picard.Homomorphisms.Quotient.Construction.FiniteLocallyFreeHom F.left ∧ AlgebraicGeometry.Surjective F.left ∧
      Picard.Homomorphisms.Quotient.Construction.IsFppfQuotientByKernel F ∧
      (∀ (l : Type) [Field l] [IsAlgClosed l] (s : Spec (.of l) ⟶ Spec (.of k)),
        Nat.card ((A.pullback s).torsionPoints q (Over.mk (𝟙 (Spec (.of l))))) = q ^ g →
          Subobject.mk ((Over.pullback s).map (Picard.Homomorphisms.Kernel.Construction.kernelInclusion F)) =
            Picard.Homomorphisms.MultiplicativeSubgroup.Construction.multiplicativePTorsion q l (A.pullback s).scheme) ∧
      Picard.Homomorphisms.Polarizations.Construction.pullbackPolarizationHom q Fact.out hS (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled D pol) =
        q • (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled D pol).hom := by
  let S : Over (Spec (.of (ZMod q))) :=
    Over.mk (Spec.map (CommRingCat.ofHom (ZMod.castHom (dvd_refl q) k)))
  have h := Picard.Homomorphisms.Theorem.Construction.relativeFrobenius_quotient_kernel_polarization q S
    (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A) (HomomorphismsPolarizationAdapter.Construction.e57PolarizationOfBundled D pol)
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.2⟩
  intro l hl hac s hcount
  let x : Picard.Homomorphisms.GeometricPoints.Construction.GeometricPoint (Spec (.of k)) := ⟨l, hl, hac, s⟩
  exact h.2.2.2.1 x ⟨g, (A.pullback s).smoothDimension, hcount⟩

/-- The quotient comparison is built from the proved fppf universal
property and identifies the actual quotient by the Frobenius kernel. -/
def e57NativeSourceQuotientIso :
    BaseChange.Construction.subgroupQuotient (Picard.Homomorphisms.Kernel.Construction.kernelInclusion
      (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q Fact.out
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) A.scheme)) ≅
      (BaseChange.Construction.fppfPoints (Spec (.of k))).obj
        (Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist q Fact.out
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) A.scheme) :=
  Quotient.Construction.kernelQuotientIsoOfHomomorphisms _ (e57NativeSourceConclusions q k D pol).2.2.1

theorem e57NativeSourceQuotientIso_projection :
    let F := Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q Fact.out
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) A.scheme
    BaseChange.Construction.relationQuotientProjection
      ((fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme F) A.scheme ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion F) *
        snd (Picard.Homomorphisms.Kernel.Construction.kernelScheme F) A.scheme)
      (snd (Picard.Homomorphisms.Kernel.Construction.kernelScheme F) A.scheme) ≫
        (e57NativeSourceQuotientIso q k D pol).hom = (BaseChange.Construction.fppfPoints (Spec (.of k))).map F :=
  Quotient.Construction.kernelQuotientIsoOfHomomorphisms_projection _ (e57NativeSourceConclusions q k D pol).2.2.1

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HomomorphismsIntrinsic.Construction

import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedKernelOrthogonal
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PairingValues

/-! # Kernel Orthogonal -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Reference.KernelOrthogonal.ReferenceSheafPoints

/-! Character-kernel sections and torsion-map kernels retain the
original HilbertConstruction torsion functor and original ambient isogeny map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PairingValues OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedKernelOrthogonal OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IsogenyComplement
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComplementCharacterSquare OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComplementCharacterSquare.KernelEmbedding

variable {k : Type} [Field k] [IsAlgClosed k] {g h N M : ℕ} {δ : Fin g → ℕ} {ε : Fin h → ℕ}
variable (PA : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (PB : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel h ε M (Spec (.of k)))
variable (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny PA.abelian PB.abelian) (n : ℕ)
variable (hk : ∀ (T : Over (Spec (.of k))) (a : T ⟶ PA.abelian.scheme), a ≫ f.hom = 1 → a ^ n = 1)

omit [IsAlgClosed k] in
theorem originalKernelPoint_killed (T : Over (Spec (.of k))) (y : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom) :
    (y ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f.hom) ≫ f.hom = 1 :=
  (Category.assoc _ _ _).trans ((congrArg (fun w => y ≫ w) (Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp f.hom)).trans (MonObj.comp_one y))

def originalKernelTorsionPoint (T : Over (Spec (.of k))) (y : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom) :
    (PA.abelian.torsionFunctor n).obj (.op T) :=
  ⟨y ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f.hom, hk T (y ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f.hom) (originalKernelPoint_killed PA PB f T y)⟩

omit [IsAlgClosed k] in
theorem originalKernelTorsionPoint_sheaf (T : Over (Spec (.of k))) (y : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom) :
    AbelianScheme.FrobeniusKernel.Prescription.Construction.originalTorsionSheafPoint PA.abelian n T (originalKernelTorsionPoint PA PB f n hk T y) =
      (PolarizedKernelOrthogonal.isogenyKernelTorsionEmbedding PA PB f n hk).hom.app (.op T) (ULift.up y) := by
  let inc := kernel.ι (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk PA.abelian.scheme)) n)
  have : Mono inc := inferInstanceAs (Mono (kernel.ι _))
  have hm : Mono (inc.hom.app (.op T)) := inferInstance
  apply (CommGrpCat.mono_iff_injective (inc.hom.app (.op T))).mp hm
  have hleft := Canonical.PairingValues.originalTorsionSheafPoint_inclusion PA.abelian n T (originalKernelTorsionPoint PA PB f n hk T y)
  have hright := congrArg (fun w => w.hom.app (.op T) (ULift.up y))
    (ComplementCharacterSquare.KernelEmbedding.complementKernelTorsionEmbedding_inclusion f.hom (IsogenyComplement.isogenyComplement f n hk) n
      (IsogenyComplement.isogenyComplement_projection f n hk))
  exact hleft.trans hright.symm

omit [IsAlgClosed k] in
theorem originalTorsionPoint_map_zero_iff (T : Over (Spec (.of k)))
    (x : (PA.abelian.torsionFunctor n).obj (.op T)) :
    (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (ComplementCharacterSquare.complementSourceGroupMap f.hom)) n).hom.app (.op T)
        (AbelianScheme.FrobeniusKernel.Prescription.Construction.originalTorsionSheafPoint PA.abelian n T x) = 1 ↔ x.val ≫ f.hom = 1 := by
  let inc := kernel.ι (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk PB.abelian.scheme)) n)
  have : Mono inc := inferInstanceAs (Mono (kernel.ι _))
  have hm : Mono (inc.hom.app (.op T)) := inferInstance
  have hinj := (CommGrpCat.mono_iff_injective (inc.hom.app (.op T))).mp hm
  have hs := congrArg (fun w => w.hom.app (.op T) (AbelianScheme.FrobeniusKernel.Prescription.Construction.originalTorsionSheafPoint PA.abelian n T x))
    (AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap_inclusion (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (ComplementCharacterSquare.complementSourceGroupMap f.hom)) n)
  have hv : inc.hom.app (.op T)
      ((AbelianScheme.CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (ComplementCharacterSquare.complementSourceGroupMap f.hom)) n).hom.app (.op T)
        (AbelianScheme.FrobeniusKernel.Prescription.Construction.originalTorsionSheafPoint PA.abelian n T x)) = ULift.up (x.val ≫ f.hom) := by
    exact hs.trans (congrArg ((AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (ComplementCharacterSquare.complementSourceGroupMap f.hom)).hom.app (.op T))
      (Canonical.PairingValues.originalTorsionSheafPoint_inclusion PA.abelian n T x))
  constructor
  · intro hz
    have h := hv.symm.trans ((congrArg (inc.hom.app (.op T)) hz).trans (inc.hom.app (.op T)).hom.map_one)
    exact congrArg ULift.down h
  · intro hz
    apply hinj
    exact hv.trans ((congrArg ULift.up hz).trans (inc.hom.app (.op T)).hom.map_one.symm)

omit [IsAlgClosed k] in
theorem originalTorsionSheafPoint_natural {T U : Over (Spec (.of k))} (t : U ⟶ T)
    (x : (PA.abelian.torsionFunctor n).obj (.op T)) :
    AbelianScheme.FrobeniusKernel.Prescription.Construction.originalTorsionSheafPoint PA.abelian n U ((PA.abelian.torsionFunctor n).map t.op x) =
      (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk PA.abelian.scheme)) n).obj.map t.op
        (AbelianScheme.FrobeniusKernel.Prescription.Construction.originalTorsionSheafPoint PA.abelian n T x) := by
  let inc := kernel.ι (AbelianScheme.CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk PA.abelian.scheme)) n)
  have : Mono inc := inferInstanceAs (Mono (kernel.ι _))
  have hm : Mono (inc.hom.app (.op U)) := inferInstance
  apply (CommGrpCat.mono_iff_injective (inc.hom.app (.op U))).mp hm
  have hleft := Canonical.PairingValues.originalTorsionSheafPoint_inclusion PA.abelian n U ((PA.abelian.torsionFunctor n).map t.op x)
  have hright := (inc.hom.naturality_apply t.op (AbelianScheme.FrobeniusKernel.Prescription.Construction.originalTorsionSheafPoint PA.abelian n T x)).trans
    (congrArg ((AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk PA.abelian.scheme)).obj.map t.op)
      (Canonical.PairingValues.originalTorsionSheafPoint_inclusion PA.abelian n T x))
  exact hleft.trans hright.symm

end AlgebraicGeometry.Isogenies.NeighborCounting.Reference.KernelOrthogonal.ReferenceSheafPoints

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Reference.KernelOrthogonal

/-! The actual canonical annihilator test, expressed in the original
torsion functor, characterizes the complete original isogeny kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.KernelOrthogonal.ReferenceSheafPoints OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedKernelOrthogonal

variable {k : Type} [Field k] [IsAlgClosed k] {g h N M : ℕ} {δ : Fin g → ℕ} {ε : Fin h → ℕ}
variable (PA : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (PB : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel h ε M (Spec (.of k)))
variable (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny PA.abelian PB.abelian) (n : ℕ) (hn : 0 < n)
variable (hk : ∀ (T : Over (Spec (.of k))) (a : T ⟶ PA.abelian.scheme), a ≫ f.hom = 1 → a ^ n = 1)

theorem canonicalKernelOrthogonal_originalPoint_iff (T : Over (Spec (.of k)))
    (x : (PA.abelian.torsionFunctor n).obj (.op T)) :
    PolarizedKernelOrthogonal.canonicalKernelOrthogonal PA PB f n hn hk T (AbelianScheme.FrobeniusKernel.Prescription.Construction.originalTorsionSheafPoint PA.abelian n T x) ↔
      ∀ (U : Over (Spec (.of k))) (t : U ⟶ T) (y : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom),
        AbelianScheme.FrobeniusKernel.Prescription.Construction.canonicalTorsionOrthogonal PA n hn U (ReferenceSheafPoints.originalKernelTorsionPoint PA PB f n hk U y)
          ((PA.abelian.torsionFunctor n).map t.op x) := by
  have hv (U : Over (Spec (.of k))) (t : U ⟶ T) (y : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom) :=
    congrArg₂
      (fun r l => AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue
        (CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (AbelianScheme.FrobeniusKernel.HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled PA.abelian) n) U
        ((AbelianScheme.FrobeniusKernel.CartierDualityCanonical.Construction.e56SourceTorsionPairing PA n hn).rightAdjoint.hom.app (.op U) r) l)
      (ReferenceSheafPoints.originalTorsionSheafPoint_natural PA n t x)
      (ReferenceSheafPoints.originalKernelTorsionPoint_sheaf PA PB f n hk U y)
  constructor
  · intro h U t y
    exact (hv U t y).trans (h U t (ULift.up y))
  · intro h U t y
    obtain ⟨y⟩ := y
    exact (hv U t y).symm.trans (h U t y)

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PA.abelian)
variable (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation PA ρ)

include hρ in
theorem polarized_original_kernel_orthogonal_iff
    (hpol : AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f.hom PA.dual PB.dual PB.polarization = PA.polarization.isogeny.hom ^ n)
    (hdegree : n.Coprime (∏ i, ε i))
    (T : Over (Spec (.of k))) (x : (PA.abelian.torsionFunctor n).obj (.op T)) :
    (∀ (U : Over (Spec (.of k))) (t : U ⟶ T) (y : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom),
      AbelianScheme.FrobeniusKernel.Prescription.Construction.canonicalTorsionOrthogonal PA n hn U (ReferenceSheafPoints.originalKernelTorsionPoint PA PB f n hk U y)
        ((PA.abelian.torsionFunctor n).map t.op x)) ↔ x.val ≫ f.hom = 1 :=
  (canonicalKernelOrthogonal_originalPoint_iff PA PB f n hn hk T x).symm.trans
    ((PolarizedKernelOrthogonal.polarized_kernel_orthogonal_iff PA PB ρ hρ f n hn hk hpol hdegree T
      (AbelianScheme.FrobeniusKernel.Prescription.Construction.originalTorsionSheafPoint PA.abelian n T x)).trans
        (ReferenceSheafPoints.originalTorsionPoint_map_zero_iff PA PB f n T x))

end AlgebraicGeometry.Isogenies.NeighborCounting.Reference.KernelOrthogonal

end

end OAI

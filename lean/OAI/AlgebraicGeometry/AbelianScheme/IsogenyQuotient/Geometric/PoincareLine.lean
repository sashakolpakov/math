import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DiagonalMultiplicationCompatibility
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PulledMultiplicationUnits
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareInterchange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.PoincareSymmetry

/-! # Poincare Line -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.PoincareLine.Construction

noncomputable section

section

/-! The original polarized Poincare line on a geometric fiber has
fully constructed horizontal and vertical products. Their interchange
and compatibility with the constructed normalized symmetry are proved. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames

variable {S : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) (n : ℕ)

def geometricPoincareHorizontalMultiplication :
    Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst (A.pullback s).scheme (A.pullback s).scheme)
      (snd (A.pullback s).scheme (A.pullback s).scheme)
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s)) ((PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) ^ n)) :=
  Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication ((PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) ^ n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication (D.pullback s))

def geometricPoincareVerticalMultiplication :
    Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd (A.pullback s).scheme (A.pullback s).scheme)
      (fst (A.pullback s).scheme (A.pullback s).scheme)
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s)) ((PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) ^ n)) :=
  Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical ((PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) ^ n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication (D.pullback s))

theorem geometricPoincareMultiplications_interchange :
    Picard.PoincareBundle.Biextension.Compatibility.Interchange
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s)) ((PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) ^ n))
      (geometricPoincareHorizontalMultiplication D pol k s n)
      (geometricPoincareVerticalMultiplication D pol k s n) :=
  Picard.PoincareBundle.Poincare.TransverseFrames.source_interchange _ _ _ _ (Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange (D.pullback s))

theorem geometricPoincareMultiplications_unit_zero (T : Over (Spec (.of k))) :
    (geometricPoincareHorizontalMultiplication D pol k s n).unitFrame
      (1 : T ⟶ (A.pullback s).scheme ⊗ (A.pullback s).scheme)
      (MonObj.one_comp (fst (A.pullback s).scheme (A.pullback s).scheme)) =
    (geometricPoincareVerticalMultiplication D pol k s n).unitFrame 1
      (MonObj.one_comp (snd (A.pullback s).scheme (A.pullback s).scheme)) :=
  PulledMultiplicationUnits.Construction.sourceMultiplications_unit_zero _ _ _ _ T (Reference.PoincareMultiplications.Construction.originalPoincareMultiplications_unit_zero (D.pullback s) T)

theorem geometricPoincareMultiplications_symmetry_vertical :
    Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s)) ((PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) ^ n))
      (geometricPoincareHorizontalMultiplication D pol k s n) (PoincareSymmetry.Construction.geometricPoincareMultipleSymmetry D pol k s n) =
      geometricPoincareVerticalMultiplication D pol k s n :=
  DiagonalMultiplicationCompatibility.Construction.secondMultiplication_eq_of_diagonal_normalization (A.pullback s).scheme _ _ _ _
    (PoincareSymmetry.Construction.geometricPoincareMultipleSymmetry_diagonal D pol k s n)
    (geometricPoincareMultiplications_unit_zero D pol k s n _)

theorem geometricPoincareMultiplications_symmetry_horizontal :
    Picard.PoincareBundle.Symmetric.TransverseFrames.returnedFirst
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s)) ((PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) ^ n))
      (geometricPoincareVerticalMultiplication D pol k s n) (PoincareSymmetry.Construction.geometricPoincareMultipleSymmetry D pol k s n) =
      geometricPoincareHorizontalMultiplication D pol k s n :=
  DiagonalMultiplicationCompatibility.Construction.returnedFirst_eq_of_diagonal_normalization (A.pullback s).scheme _ _ _ _
    (PoincareSymmetry.Construction.geometricPoincareMultipleSymmetry_diagonal D pol k s n)
    (geometricPoincareMultiplications_unit_zero D pol k s n _)

end

section

/-! The original polarization constructs an alternating native torsion
pairing through the actual Poincare frames. No multiplication structure
or symmetry compatibility equation is supplied as an additional input.
Comparison with the CartierDuality canonical polarization pairing is separate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {S : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) (n : ℕ)

def geometricPoincareNativeTorsionPairing :
    Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme (A.pullback s).scheme n)
      (B := Torsion.Groups.Construction.nativeTorsionScheme (A.pullback s).scheme n)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X) :=
  Poincare.LineDescent.Construction.poincareNativeTorsionPairing (PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication (D.pullback s)) n (PoincareSymmetry.Construction.geometricPoincareMultipleSymmetry D pol k s n)
    (geometricPoincareMultiplications_symmetry_vertical D pol k s n)
    (Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange (D.pullback s))
    (geometricPoincareMultiplications_symmetry_horizontal D pol k s n)

theorem geometricPoincareNativeTorsionPairing_alternating
    (T : Over (Spec (.of k))) (x : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme (A.pullback s).scheme n) :
    (geometricPoincareNativeTorsionPairing D pol k s n).pairValue x x = 1 :=
  Poincare.TorsionAlternation.Construction.poincareNativeTorsionPairing_alternating _ _ _ _ n _
    (geometricPoincareMultiplications_symmetry_vertical D pol k s n)
    (Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange (D.pullback s))
    (geometricPoincareMultiplications_symmetry_horizontal D pol k s n)
    (PoincareSymmetry.Construction.geometricPoincareMultipleSymmetry_diagonal D pol k s n) T x

end

/-! Native self-annihilation for the constructed geometric Poincare
pairing gives a quotient line and its actual pullback isomorphism.
The products, symmetry, and compatibility are derived from the original
polarization; the subgroup condition refers to that constructed pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {S : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) (n : ℕ)
  {B : Over (Spec (.of k))} [GrpObj B] (f : (A.pullback s).scheme ⟶ B) [IsMonHom f]
  (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ (A.pullback s).scheme), x ≫ f = 1 → x ^ n = 1)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f)
    (geometricPoincareNativeTorsionPairing D pol k s n).relativeAnnihilator F = F)
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [IsLocallyNoetherian (B ⊗ B).left]

def geometricPoincareQuotientLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B ⊗ B).left :=
  Poincare.LineDescent.Construction.nativeIsotropicQuotientLine (PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication (D.pullback s)) n (PoincareSymmetry.Construction.geometricPoincareMultipleSymmetry D pol k s n)
    (geometricPoincareMultiplications_symmetry_vertical D pol k s n)
    (Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange (D.pullback s))
    (geometricPoincareMultiplications_symmetry_horizontal D pol k s n) f hker hlag

def geometricPoincareQuotientLine_pullbackIso :
    (Scheme.Modules.pullback (f ⊗ₘ f).left).obj
      (geometricPoincareQuotientLine D pol k s n f hker hlag).sheaf ≅
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s))
        ((PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) ^ n)).sheaf :=
  Poincare.LineDescent.Construction.nativeIsotropicQuotientLine_pullbackIso (PoincareSymmetry.Construction.geometricPolarizationMap D pol k s)
    (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s)) (Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication (D.pullback s))
    (Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication (D.pullback s)) n (PoincareSymmetry.Construction.geometricPoincareMultipleSymmetry D pol k s n)
    (geometricPoincareMultiplications_symmetry_vertical D pol k s n)
    (Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange (D.pullback s))
    (geometricPoincareMultiplications_symmetry_horizontal D pol k s n) f hker hlag

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.PoincareLine.Construction

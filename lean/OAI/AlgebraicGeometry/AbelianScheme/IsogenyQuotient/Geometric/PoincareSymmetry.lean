import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionAlternation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareLine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange

/-! # Poincare Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.PoincareSymmetry.Construction

noncomputable section

/-!
The PoincareBundle line is the original HilbertConstruction Poincare sheaf. On every geometric
fiber, the original polarization constructs the diagonal-normalized
symmetry required by the PoincareBundle frame-ratio calculation, for every multiple.
The two Poincare products and their compatibility remain explicit here.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames

universe u

theorem diagonalSymmetryComparison_eq_e45 {S : Scheme.{u}} (B : Over S)
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B ⊗ B).left) :
    DiagonalLineSymmetry.Construction.diagonalSymmetryComparison B P =
      Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ B B).hom
        (⟨P.sheaf, P.locallyTrivial⟩ : Picard.PoincareBundle.Line.Bundles.LineBundle (B ⊗ B).left)
        (DiagonalLineSymmetry.Construction.groupDiagonal B) (DiagonalLineSymmetry.Construction.groupDiagonal B) (DiagonalLineSymmetry.Construction.groupDiagonal_swap B) := by
  have h := Picard.PoincareBundle.GlobalPullbackFrame.comparison_eq (β_ B B).hom
    (⟨P.sheaf, P.locallyTrivial⟩ : Picard.PoincareBundle.Line.Bundles.LineBundle (B ⊗ B).left)
    (DiagonalLineSymmetry.Construction.groupDiagonal B) (DiagonalLineSymmetry.Construction.groupDiagonal B) (DiagonalLineSymmetry.Construction.groupDiagonal_swap B)
  simpa only [DiagonalLineSymmetry.Construction.diagonalSymmetryComparison, Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison,
    Picard.PoincareBundle.Line.Fibers.fiber, NatIso.trans_app]
    using h.symm

variable {S : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) (n : ℕ)

def geometricPolarizationMap : (A.pullback s).scheme ⟶ (D.pullback s).abelian.scheme :=
  (pol.isogeny.pullback s).hom

instance geometricPolarizationMap_isMonHom : IsMonHom (geometricPolarizationMap D pol k s) :=
  (pol.isogeny.pullback s).preservesGroup

def geometricPoincareMultipleSymmetry :
    let B := (A.pullback s).scheme
    let P := Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s)) ((geometricPolarizationMap D pol k s) ^ n)
    (Scheme.Modules.pullback (β_ B B).hom.left).obj P.sheaf ≅ P.sheaf :=
  Classical.choose (Poincare.MultipleSymmetry.Construction.geometricPoincareMultiple_diagonal_symmetry D pol k s n)

set_option backward.isDefEq.respectTransparency false in
theorem geometricPoincareMultipleSymmetry_diagonal :
    let B := (A.pullback s).scheme
    let P := Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s)) ((geometricPolarizationMap D pol k s) ^ n)
    (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal B).left).mapIso (geometricPoincareMultipleSymmetry D pol k s n) =
      Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ B B).hom P (DiagonalLineSymmetry.Construction.groupDiagonal B) (DiagonalLineSymmetry.Construction.groupDiagonal B)
        (DiagonalLineSymmetry.Construction.groupDiagonal_swap B) := by
  let B := (A.pullback s).scheme
  let P := Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine (D.pullback s) ((geometricPolarizationMap D pol k s) ^ n)
  have h := (Classical.choose_spec (Poincare.MultipleSymmetry.Construction.geometricPoincareMultiple_diagonal_symmetry D pol k s n)).1
  change (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal B).left).mapIso
    (geometricPoincareMultipleSymmetry D pol k s n) = DiagonalLineSymmetry.Construction.diagonalSymmetryComparison B P at h
  exact h.trans (diagonalSymmetryComparison_eq_e45 B P)

variable
  (Dh : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst (D.pullback s).abelian.scheme (A.pullback s).scheme)
    (snd (D.pullback s).abelian.scheme (A.pullback s).scheme) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s)))
  (Dv : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd (D.pullback s).abelian.scheme (A.pullback s).scheme)
    (fst (D.pullback s).abelian.scheme (A.pullback s).scheme) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s)))
  (hv : Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s)) ((geometricPolarizationMap D pol k s) ^ n))
      (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication ((geometricPolarizationMap D pol k s) ^ n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s)) Dh)
      (geometricPoincareMultipleSymmetry D pol k s n) =
    Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical ((geometricPolarizationMap D pol k s) ^ n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s)) Dv)

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

/-- The actual frame-ratio value is alternating for the symmetry constructed from the original polarization. -/
theorem geometricPoincareKernelValue_diagonal
    {B : Over (Spec (.of k))} [GrpObj B] (f : (A.pullback s).scheme ⟶ B) [IsMonHom f]
    (hf : Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f ≫ ((geometricPolarizationMap D pol k s) ^ n) = 1)
    {T : Over (Spec (.of k))} (x : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) :
    Picard.PoincareBundle.Canonical.KernelPairing.value ((geometricPolarizationMap D pol k s) ^ n)
      (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s)) Dh Dv f hf
      (geometricPoincareMultipleSymmetry D pol k s n) hv x x = 1 :=
  Poincare.TorsionAlternation.Construction.canonicalPoincareKernelPairing_diagonal _ _ Dh Dv f hf _ hv
    (geometricPoincareMultipleSymmetry_diagonal D pol k s n) x

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.PoincareSymmetry.Construction

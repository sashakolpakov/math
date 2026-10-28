import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.MixedKoszulSheafExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Negative.ExactCochainEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulEulerDifference

/-! # Mixed Koszul Cokernel Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulCokernelEuler

noncomputable section

/-! The final cokernel of the actual mixed Koszul complex is coherent.
For a proper smooth scheme with a finite complete intersection, its
Euler characteristic is the product of the actual tensor differences. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def mixedKoszulCokernel {X : Scheme.{u}} (M : X.Modules) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) : X.Modules :=
  cokernel ((LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs).d (-1) 0)

theorem mixedKoszulCokernel_coherent {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (bs : List (LineBundleKoszulComplex.LineBundleSection X)) :
    (mixedKoszulCokernel M bs).IsQuasicoherent ∧ (mixedKoszulCokernel M bs).IsFiniteType := by
  let C := LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs
  have : (C.X (-1)).IsQuasicoherent := (LineBundleKoszulComplex.mixedLineBundleKoszulComplex_coherent M bs (-1)).1
  have : (C.X 0).IsQuasicoherent := (LineBundleKoszulComplex.mixedLineBundleKoszulComplex_coherent M bs 0).1
  have : (C.X 0).IsFiniteType := (LineBundleKoszulComplex.mixedLineBundleKoszulComplex_coherent M bs 0).2
  exact ⟨Quasicoherent.Cokernels.module_quasicoherent_cokernel (C.d (-1) 0), Quasicoherent.QuotientFiniteType.quasicoherent_cokernel_finiteType (C.d (-1) 0)⟩

theorem smoothMixedKoszulCokernel_euler
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsProper p] (g : ℕ) (hg : 0 < g) [SmoothOfRelativeDimension g p]
    (M : Line.Bundles.LineBundle X) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) (hlen : bs.length = g)
    (hfinite : (MixedKoszulGeometricSupport.mixedSectionZeroSet bs).Finite) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (mixedKoszulCokernel M.sheaf bs) =
      MixedKoszulEulerDifference.mixedLineBundleEulerDifference X bs (LineBundle.EulerShifts.lineBundleClassEuler p) (Line.Bundles.LineBundle.classOf M) := by
  have : Smooth p := SmoothOfRelativeDimension.smooth g p
  have : M.sheaf.IsQuasicoherent := M.isQuasicoherent
  have : M.sheaf.IsFiniteType := M.isFiniteType
  let C := LineBundleKoszulComplex.mixedLineBundleKoszulComplex M.sheaf bs
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hq (i : ℤ) : (C.X i).IsQuasicoherent := (LineBundleKoszulComplex.mixedLineBundleKoszulComplex_coherent M.sheaf bs i).1
  have ht (i : ℤ) : (C.X i).IsFiniteType := (LineBundleKoszulComplex.mixedLineBundleKoszulComplex_coherent M.sheaf bs i).2
  have hC := HilbertConstruction.Smooth.MixedKoszulSheafExactness.smoothMixedKoszul_sheaf_exact_negative p g M bs hlen hfinite
  have hEuler := Negative.ExactCochainEuler.proper_coherent_negative_exact_euler_sum p C hC bs.length (by omega)
    (LineBundleKoszulComplex.mixedLineBundleKoszulComplex_isZero_X M.sheaf bs _ (Or.inl (by omega)))
  exact hEuler.symm.trans (MixedKoszulEulerDifference.mixedKoszulEuler_eq_difference p M bs)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulCokernelEuler

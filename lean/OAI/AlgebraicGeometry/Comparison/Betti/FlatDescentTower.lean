import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Stability

/-! # Flat Descent Tower -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FlatDescentTower.AnalyticLocal

noncomputable section

/-! Flatness over the base descends through a faithfully flat algebra. -/

open TensorProduct

theorem flat_of_faithfullyFlat_extension (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.Flat R T] [Module.FaithfullyFlat S T] : Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  let g : S ⊗[R] N →ₗ[S] S ⊗[R] P := AlgebraTensorModule.map LinearMap.id f
  have hg : Function.Injective g := by
    apply (Module.FaithfullyFlat.lTensor_injective_iff_injective S T g).mp
    let eN := AlgebraTensorModule.cancelBaseChange R S S T N
    let eP := AlgebraTensorModule.cancelBaseChange R S S T P
    have hc : eP.toLinearMap.restrictScalars R ∘ₗ (g.lTensor T).restrictScalars R =
        f.lTensor T ∘ₗ eN.toLinearMap.restrictScalars R := by
      ext x
      change eP ((g.lTensor T) x) = (f.lTensor T) (eN x)
      induction x using TensorProduct.inductionOn with
      | add u v hu hv => simp only [map_add, hu, hv]
      | tmul t y =>
        induction y using TensorProduct.inductionOn with
        | add u v hu hv => simp only [tmul_add, map_add, hu, hv]
        | tmul s n => simp [g, eN, eP]
    intro u v huv
    apply eN.injective
    apply Module.Flat.lTensor_preserves_injective_linearMap f hf
    exact (DFunLike.congr_fun hc u).symm.trans
      ((congrArg eP huv).trans (DFunLike.congr_fun hc v))
  exact hg

end

end OAI.AlgebraicGeometry.Comparison.Betti.FlatDescentTower.AnalyticLocal

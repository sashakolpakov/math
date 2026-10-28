import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisBaseChangePoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.OpenCover

/-! # Integral Fibers -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.IntegralFibers.BundleCycles

noncomputable section

/-! Every geometric fiber of the actual projective symmetric spectrum
of a nonzero finite free module is integral. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [Nonempty ι]
    (b : Module.Basis ι R M)

include b in
theorem symmetricProjective_baseChange_isIntegral {K : Type} [Field K]
    (g : Spec (.of K) ⟶ Spec (.of R)) : IsIntegral (pullback (Scheme.BundleCycles.symmetricProjectiveToBase R M) g) := by
  let C := Symmetric.BasisBaseChangeCover.BundleCycles.symmetricBasisBaseChangeCover b g
  let : IsIntegral (pullback g (𝟙 _)) := IsIntegral.of_isIso (inv (pullback.fst g (𝟙 _)))
  have hC (i : C.I₀) : IsIntegral (C.X i) := by
    change IsIntegral (AffineSpace {j : ι // j ≠ i} (pullback g (𝟙 _)))
    infer_instance
  exact Integral.OpenCover.BundleCycles.isIntegral_of_openCover_commonPoint C hC
    (Symmetric.BasisBaseChangePoint.BundleCycles.symmetricBasisBaseChangePoint b g (genericPoint (Spec (.of K))))
    (fun i => Symmetric.BasisBaseChangePoint.BundleCycles.symmetricBasisBaseChangePoint_mem_chart b g i _)

include b in
theorem symmetricProjective_geometricallyIntegral : GeometricallyIntegral (Scheme.BundleCycles.symmetricProjectiveToBase R M) := by
  constructor
  intro K _ g Z a c h
  let := symmetricProjective_baseChange_isIntegral b g
  exact IsIntegral.of_isIso h.isoPullback.inv

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.IntegralFibers.BundleCycles

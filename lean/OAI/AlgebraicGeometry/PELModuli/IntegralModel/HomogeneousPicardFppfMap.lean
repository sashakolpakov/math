import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardLocal
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Homogeneous Picard Fppf Map -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardFppfMap

noncomputable section

/-! Homogeneity descends along one surjective fppf map of test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem homogeneousPicard_of_fppf_map {S : Scheme.{u}} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {T U : Over S} (f : U ⟶ T)
    [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
    (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (.op T))
    (hq : A.IsHomogeneousPicardClass U ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op q)) :
    A.IsHomogeneousPicardClass T q := by
  apply HomogeneousPicardLocal.homogeneousPicard_of_cover A T q (Sieve.generate (Presieve.singleton f))
  · apply (Scheme.fppfTopology.mem_over_iff _).mpr
    change (Sieve.generate (Presieve.singleton f)).functorPushforward (Over.forget S) ∈ _
    rw [← Sieve.generate_map_eq_functorPushforward, Presieve.map_singleton]
    exact Precoverage.generate_mem_toGrothendieck f.left.singleton_mem_fppfPrecoverage
  · rintro V k ⟨W, a, c, hc, rfl⟩
    cases hc
    simpa only [op_comp, Functor.map_comp_apply] using hq.pullback A a

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.HomogeneousPicardFppfMap

import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomLocalSheaf

/-! # Test Base Sieve -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.TestBaseSieve

noncomputable section

/-! A sieve on a test scheme induces a covering sieve on its identity base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (T : Over S)

def testBaseArrow (U : Over T.left) : (Over.map T.hom).obj U ⟶ T := Over.homMk U.hom rfl

theorem sliceBaseChangeSieve_mem_testBaseArrow (R : Sieve T) {U : Over T.left}
    (f : U ⟶ Over.mk (𝟙 T.left)) (hf : Module.HomLocalSheaf.sliceBaseChangeSieve T R f) :
    R (testBaseArrow T U) := by
  change (Sieve.overEquiv T R) f.left at hf
  have he : f.left = U.hom := (Category.comp_id f.left).symm.trans f.w
  have hf' : (Sieve.overEquiv T R) U.hom := he ▸ hf
  exact (Sieve.overEquiv_iff _ _).mp hf'

theorem sliceBaseChangeSieve_mem (J : GrothendieckTopology Scheme.{u}) (R : Sieve T)
    (hR : R ∈ (J.over S) T) :
    Module.HomLocalSheaf.sliceBaseChangeSieve T R ∈ (J.over T.left) (Over.mk (𝟙 T.left)) :=
  J.overEquiv_symm_mem_over _ _ hR

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.TestBaseSieve

import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverOpenCoverGluing

/-! # Test Base Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.TestBaseCover

noncomputable section

/-! The actual source cover cut out by a covering family of base opens. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme.{0}} {I : Type} (U : I → S.Opens) (hU : iSup U = ⊤) (T : Over S)

def testBaseOpenCover : T.left.OpenCover where
  I₀ := I
  X i := (T.hom ⁻¹ᵁ U i).toScheme
  f i := (T.hom ⁻¹ᵁ U i).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      have hx : T.hom x ∈ iSup U := by rw [hU]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨i, ⟨x, hi⟩, rfl⟩
    · intro i
      infer_instance

theorem testBaseOpenCover_mapsTo (i : I) (x : (testBaseOpenCover U hU T).X i) :
    (OverOpenCoverGluing.OverOpenCover.obj T (testBaseOpenCover U hU T) i).hom x ∈ U i := x.property

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.TestBaseCover

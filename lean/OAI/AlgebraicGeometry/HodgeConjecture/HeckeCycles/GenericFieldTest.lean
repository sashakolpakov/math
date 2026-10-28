import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldCompositionBase
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeFieldPoints

/-! # Generic Field Test -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GenericFieldTest.CM

noncomputable section

/-! Identify the same number-field test point through the q-adic
embedding or through the finite evaluation field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldCompositionBase.CM.Points

variable {K Q F L : Type} [Field K] [Field Q] [Field F] [Field L]
  (α : K →+* Q) (β : Q →+* F) (γ : F →+* L)

theorem base_square :
    Spec.map (CommRingCat.ofHom (γ.comp β)) ≫ Spec.map (CommRingCat.ofHom α) =
      Spec.map (CommRingCat.ofHom γ) ≫ Spec.map (CommRingCat.ofHom (β.comp α)) := by
  calc
    _ = Spec.map (CommRingCat.ofHom ((γ.comp β).comp α)) := FieldCompositionBase.CM.Points.spec_comp α (γ.comp β)
    _ = Spec.map (CommRingCat.ofHom (γ.comp (β.comp α))) := rfl
    _ = _ := (FieldCompositionBase.CM.Points.spec_comp (β.comp α) γ).symm

def testIso :
    (Over.map (Spec.map (CommRingCat.ofHom α))).obj
      (Over.mk (Spec.map (CommRingCat.ofHom (γ.comp β)))) ≅
    Over.mk (Spec.map (CommRingCat.ofHom γ) ≫ Spec.map (CommRingCat.ofHom (β.comp α))) :=
  PrimeFieldPoints.CM.testIso _ _ _ (base_square α β γ)

theorem testIso_hom_left : (testIso α β γ).hom.left = 𝟙 (Spec (.of L)) := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GenericFieldTest.CM

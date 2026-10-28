import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualRepresentingTransport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairBaseChangeProjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.FamilyTransport

/-! # Dual Transport Poincare Projection -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualTransportPoincareProjection

noncomputable section

/-! The Poincare line transported in both families is the pullback along
the literal product of their comparison maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S T : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (b : T ⟶ S) {A' D' : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g T}
    (eA : (A.pullback b).scheme ≅ A'.scheme) [IsMonHom eA.hom]
    (eD : D'.scheme ≅ (D.abelian.pullback b).scheme) [IsMonHom eD.hom]

def dualTransportPoincareProjectionIso :
    (DualRepresentingTransport.dualRepresentingTransport ((D.pullback b).familyTransport eA) eD).poincare.sheaf ≅
      (D.poincare.pullback
        ((eD.hom ⊗ₘ eA.inv).left ≫ PairBaseChangeProjection.pairBaseChangeProjection b D.abelian.scheme A.scheme)).sheaf := by
  let p := (eD.hom ▷ A'.scheme)
  let q := (𝟙 (D.abelian.pullback b).scheme ⊗ₘ eA.inv)
  let r := (D.poincarePullbackOverMap b).left
  have he : p ≫ q = eD.hom ⊗ₘ eA.inv := by
    simp [p, q, ← tensorHom_def]
  exact (Scheme.Modules.pullbackComp p.left q.left).app (D.poincarePullback b).sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left he)).app (D.poincarePullback b).sheaf ≪≫
    (Scheme.Modules.pullbackComp (eD.hom ⊗ₘ eA.inv).left r).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg (fun z => (eD.hom ⊗ₘ eA.inv).left ≫ z)
      (PairBaseChangeProjection.poincarePullbackOverMap_left b A D))).app D.poincare.sheaf

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualTransportPoincareProjection

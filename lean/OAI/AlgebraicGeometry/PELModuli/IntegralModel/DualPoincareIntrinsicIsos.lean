import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualRepresentingTransport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairBaseChangeProjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.FamilyTransport

/-! # Dual Poincare Intrinsic Isos -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualPoincareIntrinsicIsos

noncomputable section

/-! Native product pullback formulas for the actual Poincare line,
under scalar change and comparison of both abelian families. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S T : Scheme.{u}} {g : ℕ} {A B C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

def dualPullbackPoincarePairIso (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (b : T ⟶ S) :
    (D.pullback b).poincare.sheaf ≅
      (D.poincare.pullback (PairBaseChangeProjection.pairBaseChangeProjection b D.abelian.scheme A.scheme)).sheaf :=
  (Scheme.Modules.pullbackCongr (PairBaseChangeProjection.poincarePullbackOverMap_left b A D)).app D.poincare.sheaf

def dualTransportPoincareProductIso (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (eA : A.scheme ≅ B.scheme) [IsMonHom eA.hom]
    (eD : C.scheme ≅ D.abelian.scheme) [IsMonHom eD.hom] :
    (DualRepresentingTransport.dualRepresentingTransport (D.familyTransport eA) eD).poincare.sheaf ≅
      (D.poincare.pullback (eD.hom ⊗ₘ eA.inv).left).sheaf := by
  let p := eD.hom ▷ B.scheme
  let q := 𝟙 D.abelian.scheme ⊗ₘ eA.inv
  have he : p ≫ q = eD.hom ⊗ₘ eA.inv := by simp [p, q, ← tensorHom_def]
  exact (Scheme.Modules.pullbackComp p.left q.left).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left he)).app D.poincare.sheaf

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualPoincareIntrinsicIsos

import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameComplexFunctor

/-! # Frame Symbols -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FrameSymbols

noncomputable section

/-! Native frame maps preserve the literal divided-power symbols. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))
  {F G : BigCrystallineSite.Object p B J δ f} (α : F ⟶ G)

local instance sourceAlgebra : Algebra B G.ring := G.base.toAlgebra
local instance targetAlgebra : Algebra B F.ring := F.base.toAlgebra

theorem map_symbol (n : ℕ) (a : G.ring) (v : Fin n → G.ring) :
    (((GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.functor f).map α.op).f n)
        (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol B G.ring G.ideal G.dividedPowers a v) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol B F.ring F.ideal F.dividedPowers
        (α.ringMap a) (fun i => α.ringMap (v i)) :=
  AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol (CommAlgCat.ofHom (DeRham.ambientMap f α))
    (DeRham.ambientMap_isDPMorphism f α) n a v

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FrameSymbols

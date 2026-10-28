import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TransportedGenericKernel

/-! # Transported Kernel Ambient Inclusion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TransportedKernelAmbientInclusion

noncomputable section

/-! An actual commuting block-inclusion square identifies the ambient
inclusion of the transported generic kernel with the integral one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TransportedGenericKernel
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

universe u

variable {S₁ S₂ S₀ : Scheme.{u}} (f : S₀ ⟶ S₁) (g : S₀ ⟶ S₂)
  (G A : Grp (Over S₁)) (H B : Grp (Over S₂))
  (i : G ⟶ A) (j : H ⟶ B)
  (e : (Over.pullback f).mapGrp.obj G ≅ (Over.pullback g).mapGrp.obj H)
  (a : (Over.pullback f).mapGrp.obj A ≅ (Over.pullback g).mapGrp.obj B)
  (K : Kernel.Properties.FiniteFlatKernel H.X)
  (square : e.hom ≫ (Over.pullback g).mapGrp.map j =
    (Over.pullback f).mapGrp.map i ≫ a.hom)

include square in
theorem transportedKernel_ambient_inclusion :
    ((TransportedGenericKernel.transportedGenericKernel f g G H e K).inclusion ≫ (Over.pullback f).map i.hom.hom) ≫
      a.hom.hom.hom =
    (Over.pullback g).map K.inclusion ≫ (Over.pullback g).map j.hom.hom := by
  let eraw : (Over.pullback f).obj G.X ≅ (Over.pullback g).obj H.X :=
    (Grp.forget (Over S₀)).mapIso e
  let araw : (Over.pullback f).obj A.X ≅ (Over.pullback g).obj B.X :=
    (Grp.forget (Over S₀)).mapIso a
  have hs : eraw.hom ≫ (Over.pullback g).map j.hom.hom =
      (Over.pullback f).map i.hom.hom ≫ araw.hom :=
    congrArg (fun z : (Over.pullback f).mapGrp.obj G ⟶ (Over.pullback g).mapGrp.obj B =>
      z.hom.hom) square
  change (((Over.pullback g).map K.inclusion ≫ eraw.inv) ≫ (Over.pullback f).map i.hom.hom) ≫
      araw.hom = _
  rw [Category.assoc, Category.assoc, ← hs, Iso.inv_hom_id_assoc]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TransportedKernelAmbientInclusion

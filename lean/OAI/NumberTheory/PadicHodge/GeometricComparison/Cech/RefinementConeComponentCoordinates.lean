import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.RefinementOneEdge
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeRefinementComponents
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeComponentCongr

/-! # Refinement Cone Component Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.RefinementConeComponentCoordinates.CechRefinementConeComponentCoordinates

noncomputable section

/-! Separate the original degree-one edge refinement square from
its subsequent passage to homology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v s t a b
variable (R : Type u) [CommRing R]
  {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {D : Type a} [Category.{b} D] [Quiver.IsThin D] [HasBinaryProducts D]
  (F : C ⥤ D) {ι κ : Type} (U : ι → C) (V : κ → D)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)
  (K : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ)
  (M : CochainComplex (ModuleCat.{max u v} R) ℕ)

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasLimitsOfSize.{0, 0, max u v, u}
local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasColimitsOfSize.{max u v, u, 0, 0} R

variable (e : M ⟶ CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.total R V K)
  (η : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := D)).obj M ⟶ K)
  (θ : (CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := C)).obj M ⟶
    ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback F).mapHomologicalComplex (.up ℕ)).obj K)
  (he : e.f 1 = (CechPresheaf.ConeTotal.CechPresheafConeTotal.map V K M η).f 1)
  (hθ : ∀ W, ((CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F K M η).f 1).app W = (θ.f 1).app W)

include he hθ in
theorem component : e.f 1 ≫ (CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F U V r K).f 1 =
    (CechPresheaf.ConeTotal.CechPresheafConeTotal.map U
      (((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback F).mapHomologicalComplex (.up ℕ)).obj K) M θ).f 1 :=
  (congrArg (fun a => a ≫ (CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F U V r K).f 1) he).trans
    ((CechPresheaf.ConeRefinementComponents.CechPresheafConeRefinementComponents.augmentation F U V r K M η 1).trans
      (CechPresheaf.ConeComponentCongr.CechPresheafConeComponentCongr.component U _ M
        (CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F K M η) θ 1 hθ))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.RefinementConeComponentCoordinates.CechRefinementConeComponentCoordinates

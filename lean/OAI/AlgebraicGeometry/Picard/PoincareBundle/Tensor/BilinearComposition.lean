import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointIsoUnits

/-! # Bilinear Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.BilinearComposition

noncomputable section

/-!
# Composition of the canonical bilinear pullback adjoints
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Iterated direct image of bilinear maps agrees through the actual direct-image composition isomorphism. -/
theorem pushforward_comp {M N P : X.Modules} (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) :
    ((β.pushforward f).pushforward g).postcomp ((Scheme.Modules.pushforwardComp f g).hom.app P) =
      (β.pushforward (f ≫ g)).precomp ((Scheme.Modules.pushforwardComp f g).hom.app M)
        ((Scheme.Modules.pushforwardComp f g).hom.app N) := by
  apply AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

/-- The two iterated pullback units are the unit of the composite through the canonical comparisons. -/
theorem unit_composition (M : Z.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
      (Scheme.Modules.pushforward g).map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback g).obj M))) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app
        ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)) =
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
      (Scheme.Modules.pushforward (f ≫ g)).map ((Scheme.Modules.pullbackComp f g).inv.app M) := by
  have h := AdjointIsoUnits.unit_transport
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) (Scheme.Modules.pullbackComp f g)
    (Scheme.Modules.pushforwardComp f g) (Scheme.Modules.conjugateEquiv_pullbackComp_inv f g) M
  have ht := congrArg (fun t => t ≫
    (Scheme.Modules.pushforward (f ≫ g)).map ((Scheme.Modules.pullbackComp f g).inv.app M)) h
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at ht
  exact ht

/-- The actual unit-defined bilinear adjoints respect composition of geometric pullback. -/
theorem bilinearAdjoint_comp (M N : Z.Modules) {P : X.Modules}
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M))
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N)) P) :
    (PullbackMap.bilinearAdjoint g M N (PullbackMap.bilinearAdjoint f ((Scheme.Modules.pullback g).obj M)
      ((Scheme.Modules.pullback g).obj N) β)).postcomp ((Scheme.Modules.pushforwardComp f g).hom.app P) =
    PullbackMap.bilinearAdjoint (f ≫ g) M N (β.precomp ((Scheme.Modules.pullbackComp f g).inv.app M)
      ((Scheme.Modules.pullbackComp f g).inv.app N)) := by
  unfold PullbackMap.bilinearAdjoint
  rw [PullbackMap.pushforward_precomp, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_comp, ← AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_postcomp, pushforward_comp,
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_comp, PullbackMap.pushforward_precomp, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_comp, unit_composition f g M, unit_composition f g N]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.BilinearComposition

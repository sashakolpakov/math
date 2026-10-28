import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap

/-! # Open Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.OpenPullback

noncomputable section

/-!
# The canonical tensor comparison is invertible for open pullback
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

section

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap

/-- Isomorphisms of the two input sheaves give an equivalence of bilinear maps. -/
def bilinearPrecompEquiv {X : Scheme.{u}} {M M' N N' P : X.Modules} (a : M' ≅ M) (b : N' ≅ N) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P ≃ AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M' N' P where
  toFun β := β.precomp a.hom b.hom
  invFun β := β.precomp a.inv b.inv
  left_inv β := by
    dsimp only
    rw [AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_comp, a.inv_hom_id, b.inv_hom_id, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_id]
  right_inv β := by
    dsimp only
    rw [AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_comp, a.hom_inv_id, b.hom_inv_id, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_id]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- The units of restriction and pullback agree through their actual uniqueness isomorphism. -/
theorem unit_comparison (M : Y.Modules) :
    (Scheme.Modules.restrictAdjunction f).unit.app M ≫ (Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictFunctorIsoPullback f).app M).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) M

/-- The canonical bilinear adjoint for open pullback is the actual restriction adjunction. -/
theorem bilinearAdjoint_eq_restrict (M N : Y.Modules) {P : X.Modules}
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) P) :
    PullbackMap.bilinearAdjoint f M N β = AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrictHomEquiv f M N P
      (β.precomp ((Scheme.Modules.restrictFunctorIsoPullback f).app M).hom
        ((Scheme.Modules.restrictFunctorIsoPullback f).app N).hom) := by
  change _ = ((β.precomp _ _).pushforward f).precomp _ _
  rw [PullbackMap.pushforward_precomp, AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_comp, unit_comparison f M, unit_comparison f N]
  rfl

/-- For an open immersion, the actual canonical bilinear adjoint is an equivalence. -/
def bilinearAdjointEquiv (M N : Y.Modules) (P : X.Modules) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) P ≃
      AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N ((Scheme.Modules.pushforward f).obj P) :=
  (bilinearPrecompEquiv ((Scheme.Modules.restrictFunctorIsoPullback f).app M)
    ((Scheme.Modules.restrictFunctorIsoPullback f).app N)).trans (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrictHomEquiv f M N P)

/-- The equivalence uses precisely the unit-defined map, so it identifies the canonical comparison. -/
theorem bilinearAdjointEquiv_apply (M N : Y.Modules) (P : X.Modules)
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) P) :
    bilinearAdjointEquiv f M N P β = PullbackMap.bilinearAdjoint f M N β :=
  (bilinearAdjoint_eq_restrict f M N β).symm

end

section

/-- Bijectivity of precomposition into every target constructs an actual two-sided inverse. -/
theorem isIso_of_precomp_bijective {C : Type*} [Category C] {A B : C} (a : A ⟶ B)
    (h : ∀ P : C, Function.Bijective (fun t : B ⟶ P => a ≫ t)) : IsIso a := by
  obtain ⟨b, hb⟩ := (h A).surjective (𝟙 A)
  change a ≫ b = 𝟙 A at hb
  have hb' : b ≫ a = 𝟙 B := (h B).injective (by rw [← Category.assoc, hb, Category.id_comp, Category.comp_id])
  exact ⟨⟨b, hb, hb'⟩⟩

end

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- The canonical tensor comparison for an open immersion is an isomorphism. -/
theorem pullbackMap_isIso (M N : Y.Modules) : IsIso (PullbackMap.pullbackMap f M N) := by
  apply isIso_of_precomp_bijective
  intro P
  let e := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) P).trans
    (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N ((Scheme.Modules.pushforward f).obj P))
  let d := (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) P).trans
    (bilinearAdjointEquiv f M N P)
  have he : (fun t => e (PullbackMap.pullbackMap f M N ≫ t)) = d := by
    funext t
    exact (PullbackMap.pullbackMap_postcomp f M N t).trans (bilinearAdjointEquiv_apply f M N P _).symm
  constructor
  · intro x y hxy
    apply d.injective
    rw [← congrFun he x, ← congrFun he y]
    exact congrArg e hxy
  · intro x
    obtain ⟨y, hy⟩ := d.surjective (e x)
    exact ⟨y, e.injective ((congrFun he y).trans hy)⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.OpenPullback

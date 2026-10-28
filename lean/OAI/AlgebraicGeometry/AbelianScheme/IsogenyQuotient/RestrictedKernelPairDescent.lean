import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.PairDescent

/-! # Restricted Kernel Pair Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RestrictedKernelPairDescent.Construction.KernelPairDescent

noncomputable section

/-! Transport need only be constructed on a class of test objects
containing the source, kernel pair, and triple overlap. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X Y : C} (f : X ⟶ Y)
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) (L : F.obj (.mk (op X)))
  (P : C → Prop)
  (τ : ∀ {T : C}, P T → ∀ (x y : T ⟶ X), x ≫ f = y ≫ f → (Kernel.PairDescent.Construction.KernelPairDescent.pointObject F L x ⟶ Kernel.PairDescent.Construction.KernelPairDescent.pointObject F L y))
  (hself : ∀ {T : C} (hT : P T) (x : T ⟶ X), τ hT x x rfl = 𝟙 _)
  (hcomp : ∀ {T : C} (hT : P T) (x y z : T ⟶ X) (hxy : x ≫ f = y ≫ f) (hyz : y ≫ f = z ≫ f),
    τ hT x y hxy ≫ τ hT y z hyz = τ hT x z (hxy.trans hyz))
  (hnat : ∀ {T U : C} (hT : P T) (hU : P U) (t : U ⟶ T) (x y : T ⟶ X)
    (h : x ≫ f = y ≫ f) (x' y' : U ⟶ X) (hx : t ≫ x = x') (hy : t ≫ y = y')
    (h' : x' ≫ f = y' ≫ f), pullHom (τ hT x y h) t x' y' hx hy = τ hU x' y' h')
  (hX : P X) (hR : P (Kernel.PairCechMaps.Construction.KernelPairDescent.Relation f)) (hT : P (Kernel.PairCechMaps.Construction.KernelPairDescent.Triple f))

def restrictedGluingIso : Kernel.PairDescent.Construction.KernelPairDescent.pointObject F L (pullback.fst f f) ≅ Kernel.PairDescent.Construction.KernelPairDescent.pointObject F L (pullback.snd f f) where
  hom := τ hR _ _ pullback.condition
  inv := τ hR _ _ pullback.condition.symm
  hom_inv_id := (hcomp hR _ _ _ _ _).trans (hself hR _)
  inv_hom_id := (hcomp hR _ _ _ _ _).trans (hself hR _)

def ofRestrictedTransport : Kernel.PairDescent.Construction.KernelPairDescent.Datum f F L where
  gluingIso := restrictedGluingIso f F L P τ hself hcomp hR
  unit := (hnat hR hX (Kernel.PairCechMaps.Construction.KernelPairDescent.diagonal f) _ _ pullback.condition _ _ (Kernel.PairCechMaps.Construction.KernelPairDescent.diagonal_fst f) (Kernel.PairCechMaps.Construction.KernelPairDescent.diagonal_snd f) rfl).trans
    (hself hX (𝟙 X))
  cocycle := by
    have h₁ : Kernel.PairCechMaps.Construction.KernelPairDescent.source f ≫ f = Kernel.PairCechMaps.Construction.KernelPairDescent.middle f ≫ f := by
      change (Kernel.PairCechMaps.Construction.KernelPairDescent.first f ≫ pullback.fst f f) ≫ f = (Kernel.PairCechMaps.Construction.KernelPairDescent.first f ≫ pullback.snd f f) ≫ f
      rw [Category.assoc, pullback.condition, ← Category.assoc]
    have h₂ : Kernel.PairCechMaps.Construction.KernelPairDescent.middle f ≫ f = Kernel.PairCechMaps.Construction.KernelPairDescent.target f ≫ f := by
      rw [← Kernel.PairCechMaps.Construction.KernelPairDescent.second_middle]
      change (Kernel.PairCechMaps.Construction.KernelPairDescent.second f ≫ pullback.fst f f) ≫ f = (Kernel.PairCechMaps.Construction.KernelPairDescent.second f ≫ pullback.snd f f) ≫ f
      rw [Category.assoc, pullback.condition, ← Category.assoc]
    change pullHom (τ hR _ _ pullback.condition) _ _ _ _ _ ≫
      pullHom (τ hR _ _ pullback.condition) _ _ _ _ _ =
      pullHom (τ hR _ _ pullback.condition) _ _ _ _ _
    rw [hnat hR hT (Kernel.PairCechMaps.Construction.KernelPairDescent.first f) _ _ pullback.condition _ _ rfl rfl h₁,
      hnat hR hT (Kernel.PairCechMaps.Construction.KernelPairDescent.second f) _ _ pullback.condition _ _ (Kernel.PairCechMaps.Construction.KernelPairDescent.second_middle f) rfl h₂,
      hnat hR hT (Kernel.PairCechMaps.Construction.KernelPairDescent.outer f) _ _ pullback.condition _ _ (Kernel.PairCechMaps.Construction.KernelPairDescent.outer_source f) (Kernel.PairCechMaps.Construction.KernelPairDescent.outer_target f) (h₁.trans h₂)]
    exact hcomp hT _ _ _ h₁ h₂

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RestrictedKernelPairDescent.Construction.KernelPairDescent

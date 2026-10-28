import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionTensorMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorComparisonNaturality

/-! # Section Parameter Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionParameterNaturality

noncomputable section

/-! The canonical product pairing is natural in the parameter sheaf. In particular it can be transported along a frame without changing the sectionwise construction. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

variable {R : Type u} [CommRing R]
variable {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
variable (cX : R →+* Γ(X, ⊤)) (cY : R →+* Γ(Y, ⊤))
variable (hc : a.appTop.hom.comp cX = b.appTop.hom.comp cY)
variable (M : X.Modules) {N N' : Y.Modules} (e : N ⟶ N')

theorem externalSectionTensorMap_parameter_naturality (V : X.Opens)
    (n : (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op ⊤))
    (m : (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).obj (op V)) :
    SectionTensorMap.externalSectionTensorMap a b cX cY hc M N' V
        (((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor cY).map e).app (op ⊤) n ⊗ₜ[R] m) =
      ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor cX).map
        ((Scheme.Modules.pushforward a).map
          (Tensor.Bifunctor.tensorModuleMap (𝟙 ((Scheme.Modules.pullback a).obj M))
            ((Scheme.Modules.pullback b).map e)))).app (op V)
              (SectionTensorMap.externalSectionTensorMap a b cX cY hc M N V (n ⊗ₜ[R] m)) := by
  let W := a ⁻¹ᵁ V
  let Ma := (Scheme.Modules.pullback a).obj M
  let Nb := (Scheme.Modules.pullback b).obj N
  let Nb' := (Scheme.Modules.pullback b).obj N'
  let eb := (Scheme.Modules.pullback b).map e
  let s : Γ(Ma, W) := ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app V m
  let t : Γ(Nb, ⊤) := ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app N).app ⊤ n
  have hu : eb.app ⊤ t =
      ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app N').app ⊤ (e.app ⊤ n) :=
    (ConcreteCategory.congr_hom
      (congr_app (Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap_natural b cY e) (op ⊤)) n).symm
  have hr : eb.app W (Nb.presheaf.map W.leTop.op t) =
      Nb'.presheaf.map W.leTop.op (eb.app ⊤ t) :=
    ConcreteCategory.congr_hom (eb.mapPresheaf.naturality W.leTop.op) t
  have hn := hr.trans (congrArg (Nb'.presheaf.map W.leTop.op) hu)
  have ht := congrArg
    (fun β : Bilinear.Sheaves.SheafBilinearMap Ma Nb (Tensor.ProductSheaf.tensorModule Ma Nb') =>
      β.app W s (Nb.presheaf.map W.leTop.op t))
    (Tensor.Bifunctor.tensorModuleMap_spec (𝟙 Ma) eb)
  change (Tensor.Bifunctor.tensorModuleMap (𝟙 Ma) eb).app W
      ((Tensor.Bifunctor.tensorBilinear Ma Nb).app W s (Nb.presheaf.map W.leTop.op t)) =
    (Tensor.Bifunctor.tensorBilinear Ma Nb').app W s (eb.app W (Nb.presheaf.map W.leTop.op t)) at ht
  rw [hn] at ht
  let n' : (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N').obj (op ⊤) := e.app ⊤ n
  have hleft := SectionTensorMap.externalSectionTensorMap_tmul a b cX cY hc M N' V n' m
  have hright := SectionTensorMap.externalSectionTensorMap_tmul a b cX cY hc M N V n m
  exact hleft.trans (ht.symm.trans
    (congrArg (fun z : Γ(Tensor.ProductSheaf.tensorModule Ma Nb, W) =>
      (Tensor.Bifunctor.tensorModuleMap (𝟙 Ma) eb).app W z) hright).symm)

theorem externalSectionCechTensorMap_parameter_naturality
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    SectionTensorMap.externalSectionCechTensorMap a b cX cY hc M N U ≫
        (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor cX U).map
          ((Scheme.Modules.pushforward a).map
            (Tensor.Bifunctor.tensorModuleMap (𝟙 ((Scheme.Modules.pullback a).obj M))
              ((Scheme.Modules.pullback b).map e))) =
      Tensor.CochainBicomplex.tensorCochainMap (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex cX M U)
        (ModuleCat.ofHom (((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor cY).map e).app (op ⊤)).hom) ≫
          SectionTensorMap.externalSectionCechTensorMap a b cX cY hc M N' U := by
  exact Cech.TensorComparisonNaturality.CechTensorComparison.map_naturality
    ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op ⊤))
    ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N').obj (op ⊤)) cX M _ _ U
    (((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor cY).map e).app (op ⊤)).hom
    ((Scheme.Modules.pushforward a).map
      (Tensor.Bifunctor.tensorModuleMap (𝟙 ((Scheme.Modules.pullback a).obj M)) ((Scheme.Modules.pullback b).map e)))
    (SectionTensorMap.externalSectionTensorMap a b cX cY hc M N)
    (SectionTensorMap.externalSectionTensorMap a b cX cY hc M N')
    (fun V n m => (externalSectionTensorMap_parameter_naturality a b cX cY hc M e V n m).symm)
    (fun _ _ i n m => SectionTensorMap.externalSectionTensorMap_naturality a b cX cY hc M N i n m)
    (fun _ _ i n m => SectionTensorMap.externalSectionTensorMap_naturality a b cX cY hc M N' i n m)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionParameterNaturality

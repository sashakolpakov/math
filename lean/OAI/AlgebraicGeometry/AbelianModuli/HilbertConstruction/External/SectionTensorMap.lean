import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.BilinearSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorComplex

/-! # Section Tensor Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionTensorMap

noncomputable section

/-! The canonical product section pairing for a span of schemes over a coefficient ring. Global sections on the parameter scheme tensor local sections on the other factor into the actual external tensor sheaf. The pairing respects restriction and therefore gives a Cech cochain map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

variable {R : Type u} [CommRing R]

def coefficientPullbackGlobalSectionMap
    {Y P : Scheme.{u}} (b : P ⟶ Y) (cY : R →+* Γ(Y, ⊤)) (cP : R →+* Γ(P, ⊤))
    (hc : b.appTop.hom.comp cY = cP) (N : Y.Modules) :
    (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op ⊤) →ₗ[R]
      (Coefficient.ModulePresheaf.coefficientModulePresheaf cP ((Scheme.Modules.pullback b).obj N)).obj (op ⊤) := by
  subst cP
  exact Coefficient.PullbackSectionValues.coefficientPullbackSectionValueMap b cY N ⊤

theorem coefficientPullbackGlobalSectionMap_apply
    {Y P : Scheme.{u}} (b : P ⟶ Y) (cY : R →+* Γ(Y, ⊤)) (cP : R →+* Γ(P, ⊤))
    (hc : b.appTop.hom.comp cY = cP) (N : Y.Modules)
    (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op ⊤)) :
    coefficientPullbackGlobalSectionMap b cY cP hc N x =
      ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app N).app ⊤ x := by
  subst cP
  rfl

variable {X Y P : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y)
variable (cX : R →+* Γ(X, ⊤)) (cY : R →+* Γ(Y, ⊤))
variable (hc : a.appTop.hom.comp cX = b.appTop.hom.comp cY)
variable (M : X.Modules) (N : Y.Modules)

def externalSectionTensorMap (V : X.Opens) :
    TensorProduct R ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op ⊤))
      ((Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).obj (op V)) →ₗ[R]
        (Coefficient.ModulePresheaf.coefficientModulePresheaf cX ((Scheme.Modules.pushforward a).obj
          (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N)))).obj
            (op V) := by
  let cP := a.appTop.hom.comp cX
  let W := a ⁻¹ᵁ V
  let Ma := (Scheme.Modules.pullback a).obj M
  let Nb := (Scheme.Modules.pullback b).obj N
  let nMap := ((Coefficient.ModulePresheaf.coefficientModulePresheaf cP Nb).map W.leTop.op).hom.comp
    (coefficientPullbackGlobalSectionMap b cY cP hc.symm N)
  let mMap := Coefficient.PullbackSectionValues.coefficientPullbackSectionValueMap a cX M V
  let β := (Coefficient.BilinearSections.coefficientTensorSectionPairing cP Ma Nb W).flip.compl₁₂ nMap mMap
  exact (Coefficient.PushforwardModuleComparison.coefficientPushforwardModuleComponent a cX (Tensor.ProductSheaf.tensorModule Ma Nb) V).symm.toLinearMap.comp
    (TensorProduct.lift β)

theorem externalSectionTensorMap_tmul (V : X.Opens)
    (n : (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op ⊤))
    (m : (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).obj (op V)) :
    externalSectionTensorMap a b cX cY hc M N V (n ⊗ₜ[R] m) =
      (Tensor.Bifunctor.tensorBilinear ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N)).app
        (a ⁻¹ᵁ V) (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app V m)
        (((Scheme.Modules.pullback b).obj N).presheaf.map (a ⁻¹ᵁ V).leTop.op
          (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app N).app ⊤ n)) := by
  change (Tensor.Bifunctor.tensorBilinear ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N)).app
      (a ⁻¹ᵁ V) (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app V m)
      (((Scheme.Modules.pullback b).obj N).presheaf.map (a ⁻¹ᵁ V).leTop.op
        (coefficientPullbackGlobalSectionMap b cY (a.appTop.hom.comp cX) hc.symm N n)) = _
  rw [coefficientPullbackGlobalSectionMap_apply]

theorem externalSectionTensorMap_naturality {U V : X.Opens} (i : V ⟶ U)
    (n : (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op ⊤))
    (m : (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).obj (op U)) :
    externalSectionTensorMap a b cX cY hc M N V
        (n ⊗ₜ[R] (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).map i.op m) =
      (Coefficient.ModulePresheaf.coefficientModulePresheaf cX ((Scheme.Modules.pushforward a).obj
        (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N)))).map i.op
          (externalSectionTensorMap a b cX cY hc M N U (n ⊗ₜ[R] m)) := by
  let j : a ⁻¹ᵁ V ⟶ a ⁻¹ᵁ U := (TopologicalSpace.Opens.map a.base).map i
  let Ma := (Scheme.Modules.pullback a).obj M
  let Nb := (Scheme.Modules.pullback b).obj N
  let u := (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M
  let v : Γ(Nb, ⊤) := ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app N).app ⊤ n
  have hm : Ma.presheaf.map j.op (u.app U m) = u.app V (M.presheaf.map i.op m) :=
    (ConcreteCategory.congr_hom ((Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap a cX M).naturality i.op) m).symm
  have hn : Nb.presheaf.map j.op (Nb.presheaf.map (a ⁻¹ᵁ U).leTop.op v) =
      Nb.presheaf.map (a ⁻¹ᵁ V).leTop.op v := by
    change (Nb.presheaf.map (a ⁻¹ᵁ U).leTop.op ≫ Nb.presheaf.map j.op) v = _
    rw [← Nb.presheaf.map_comp]
    exact ConcreteCategory.congr_hom (congrArg Nb.presheaf.map (Subsingleton.elim _ _)) v
  have h := (Tensor.Bifunctor.tensorBilinear Ma Nb).naturality j (u.app U m)
    (Nb.presheaf.map (a ⁻¹ᵁ U).leTop.op v)
  rw [hm, hn] at h
  rw [externalSectionTensorMap_tmul, externalSectionTensorMap_tmul]
  exact h.symm

def externalSectionCechTensorMap {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    Module.TensorFunctor.ModuleTensorFunctor.complex ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op ⊤))
      (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex cX M U) ⟶
        Ordered.CoefficientCechComplex.orderedCoefficientCechComplex cX ((Scheme.Modules.pushforward a).obj
          (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N))) U :=
  OrderedCech.TensorComplex.CechTensorComparison.map ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op ⊤)) cX M _ U
    (externalSectionTensorMap a b cX cY hc M N)
    (fun _ _ i n m => externalSectionTensorMap_naturality a b cX cY hc M N i n m)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionTensorMap

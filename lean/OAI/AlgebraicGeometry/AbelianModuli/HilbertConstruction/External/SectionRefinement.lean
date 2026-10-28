import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionTensorMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackSectionPairing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PushforwardPullbackRefinement
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareSectionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorComparisonNaturality

/-! # Section Refinement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionRefinement

noncomputable section

/-! The canonical external section pairing commutes with a refinement of the parameter scheme. The maps are constructed from the actual pullback units and the commutative square. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

variable {X Y Y' P Q : Scheme.{u}}
variable (a : P ⟶ X) (b : P ⟶ Y) (d : Q ⟶ P) (j : Y' ⟶ Y) (b' : Q ⟶ Y')
variable (h : d ≫ b = b' ≫ j) (M : X.Modules) (N : Y.Modules)

def externalTensorRefinementComparison :
    (Scheme.Modules.pullback d).obj
        (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N)) ⟶
      Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback (d ≫ a)).obj M)
        ((Scheme.Modules.pullback b').obj ((Scheme.Modules.pullback j).obj N)) :=
  Tensor.PullbackComparison.tensorPullbackComparison d ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N) ≫
    Tensor.Bifunctor.tensorModuleMap ((Scheme.Modules.pullbackComp d a).hom.app M)
      ((Pullback.SquareMapEquality.modulePullbackSquareIso b b' j d h).hom.app N)

theorem externalTensorRefinementComparison_isIso [IsOpenImmersion d] :
    IsIso (externalTensorRefinementComparison a b d j b' h M N) := by
  dsimp only [externalTensorRefinementComparison]
  infer_instance

def externalTensorRefinementIso [IsOpenImmersion d] :
    (Scheme.Modules.pullback d).obj
        (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N)) ≅
      Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback (d ≫ a)).obj M)
        ((Scheme.Modules.pullback b').obj ((Scheme.Modules.pullback j).obj N)) := by
  have := externalTensorRefinementComparison_isIso a b d j b' h M N
  exact asIso (externalTensorRefinementComparison a b d j b' h M N)

def externalPushforwardRefinementMap :
    (Scheme.Modules.pushforward a).obj
        (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N)) ⟶
      (Scheme.Modules.pushforward (d ≫ a)).obj
        (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback (d ≫ a)).obj M)
          ((Scheme.Modules.pullback b').obj ((Scheme.Modules.pullback j).obj N))) :=
  PushforwardPullbackRefinement.pushforwardPullbackRefinementMap d a
      (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N)) ≫
    (Scheme.Modules.pushforward (d ≫ a)).map
      (externalTensorRefinementComparison a b d j b' h M N)

variable {R : Type u} [CommRing R]
variable (cX : R →+* Γ(X, ⊤)) (cY : R →+* Γ(Y, ⊤))
variable (hc : a.appTop.hom.comp cX = b.appTop.hom.comp cY)

include h hc in
theorem externalSection_refinement_coefficients :
    (d ≫ a).appTop.hom.comp cX = b'.appTop.hom.comp (j.appTop.hom.comp cY) := by
  ext r
  change d.appTop (a.appTop (cX r)) = b'.appTop (j.appTop (cY r))
  rw [show a.appTop (cX r) = b.appTop (cY r) from DFunLike.congr_fun hc r]
  exact congrArg (fun f : Q ⟶ Y => f.appTop (cY r)) h

theorem externalSectionTensorMap_refinement (V : X.Opens)
    (n : (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op ⊤))
    (m : (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).obj (op V)) :
    ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor cX).map
      (externalPushforwardRefinementMap a b d j b' h M N)).app (op V)
        (SectionTensorMap.externalSectionTensorMap a b cX cY hc M N V (n ⊗ₜ[R] m)) =
      SectionTensorMap.externalSectionTensorMap (d ≫ a) b' cX (j.appTop.hom.comp cY)
        (externalSection_refinement_coefficients a b d j b' h cX cY hc)
        M ((Scheme.Modules.pullback j).obj N) V
          (SectionTensorMap.coefficientPullbackGlobalSectionMap j cY (j.appTop.hom.comp cY) rfl N n ⊗ₜ[R] m) := by
  let Ma := (Scheme.Modules.pullback a).obj M
  let Nb := (Scheme.Modules.pullback b).obj N
  let M' := (Scheme.Modules.pullback (d ≫ a)).obj M
  let N' := (Scheme.Modules.pullback b').obj ((Scheme.Modules.pullback j).obj N)
  let W := a ⁻¹ᵁ V
  let W' := (d ≫ a) ⁻¹ᵁ V
  let s : Γ(Ma, W) := ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app V m
  let t : Γ(Nb, W) := Nb.presheaf.map W.leTop.op
    (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app N).app ⊤ n)
  let s' : Γ((Scheme.Modules.pullback d).obj Ma, W') :=
    ((Scheme.Modules.pullbackPushforwardAdjunction d).unit.app Ma).app W s
  let t' : Γ((Scheme.Modules.pullback d).obj Nb, W') :=
    ((Scheme.Modules.pullbackPushforwardAdjunction d).unit.app Nb).app W t
  let eM := (Scheme.Modules.pullbackComp d a).hom.app M
  let eN := (Pullback.SquareMapEquality.modulePullbackSquareIso b b' j d h).hom.app N
  have hm : eM.app W' s' =
      ((Scheme.Modules.pullbackPushforwardAdjunction (d ≫ a)).unit.app M).app V m :=
    Pullback.UnitCompositionValues.pullbackUnit_comp_value d a M V m
  have hn : eN.app W' t' = N'.presheaf.map W'.leTop.op
      (((Scheme.Modules.pullbackPushforwardAdjunction b').unit.app
        ((Scheme.Modules.pullback j).obj N)).app ⊤
          (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N).app ⊤ n)) :=
    Pullback.SquareSectionValues.modulePullbackSquareIso_unit_restrict b b' j d h N W n
  have ht := congrArg
    (fun β : Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback d).obj Ma)
      ((Scheme.Modules.pullback d).obj Nb) (Tensor.ProductSheaf.tensorModule M' N') => β.app W' s' t')
    (Tensor.Bifunctor.tensorModuleMap_spec eM eN)
  change (Tensor.Bifunctor.tensorModuleMap eM eN).app W'
      ((Tensor.Bifunctor.tensorBilinear ((Scheme.Modules.pullback d).obj Ma)
        ((Scheme.Modules.pullback d).obj Nb)).app W' s' t') =
    (Tensor.Bifunctor.tensorBilinear M' N').app W' (eM.app W' s') (eN.app W' t') at ht
  rw [hm, hn] at ht
  rw [SectionTensorMap.externalSectionTensorMap_tmul, SectionTensorMap.externalSectionTensorMap_tmul,
    SectionTensorMap.coefficientPullbackGlobalSectionMap_apply]
  change (Tensor.Bifunctor.tensorModuleMap eM eN).app W'
      ((Tensor.PullbackComparison.tensorPullbackComparison d Ma Nb).app W'
        (((Scheme.Modules.pullbackPushforwardAdjunction d).unit.app (Tensor.ProductSheaf.tensorModule Ma Nb)).app W
          ((Tensor.Bifunctor.tensorBilinear Ma Nb).app W s t))) = _
  have hp := Tensor.PullbackSectionPairing.tensorPullbackComparison_pairing d Ma Nb W s t
  exact (congrArg
    (fun v : Γ(Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback d).obj Ma)
      ((Scheme.Modules.pullback d).obj Nb), W') => (Tensor.Bifunctor.tensorModuleMap eM eN).app W' v) hp).trans ht

theorem externalSectionCechTensorMap_refinement
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    SectionTensorMap.externalSectionCechTensorMap a b cX cY hc M N U ≫
        (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor cX U).map
          (externalPushforwardRefinementMap a b d j b' h M N) =
      Tensor.CochainBicomplex.tensorCochainMap (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex cX M U)
        (ModuleCat.ofHom (SectionTensorMap.coefficientPullbackGlobalSectionMap j cY (j.appTop.hom.comp cY) rfl N)) ≫
          SectionTensorMap.externalSectionCechTensorMap (d ≫ a) b' cX (j.appTop.hom.comp cY)
            (externalSection_refinement_coefficients a b d j b' h cX cY hc)
            M ((Scheme.Modules.pullback j).obj N) U := by
  exact Cech.TensorComparisonNaturality.CechTensorComparison.map_naturality
    ((Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (op ⊤))
    ((Coefficient.ModulePresheaf.coefficientModulePresheaf (j.appTop.hom.comp cY) ((Scheme.Modules.pullback j).obj N)).obj (op ⊤))
    cX M _ _ U (SectionTensorMap.coefficientPullbackGlobalSectionMap j cY (j.appTop.hom.comp cY) rfl N)
    (externalPushforwardRefinementMap a b d j b' h M N)
    (SectionTensorMap.externalSectionTensorMap a b cX cY hc M N)
    (SectionTensorMap.externalSectionTensorMap (d ≫ a) b' cX (j.appTop.hom.comp cY)
      (externalSection_refinement_coefficients a b d j b' h cX cY hc)
      M ((Scheme.Modules.pullback j).obj N))
    (fun V n m => externalSectionTensorMap_refinement a b d j b' h M N cX cY hc V n m)
    (fun _ _ i n m => SectionTensorMap.externalSectionTensorMap_naturality a b cX cY hc M N i n m)
    (fun _ _ i n m => SectionTensorMap.externalSectionTensorMap_naturality (d ≫ a) b' cX (j.appTop.hom.comp cY)
      (externalSection_refinement_coefficients a b d j b' h cX cY hc)
      M ((Scheme.Modules.pullback j).obj N) i n m)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionRefinement

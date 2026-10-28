import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientExternalSectionPairing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionRefinement
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.RestrictedSectionComposition

/-! # Ambient External Pullback Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientExternalPullbackComparison

noncomputable section

/-! Pulling the ambient pairing to a refined parameter chart gives the canonical external pairing there, for locally defined parameter sections. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
universe u

theorem tensorPullbackComparison_pairing_on
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules)
    (U : Y.Opens) (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ U) (m : Γ(M, U)) (n : Γ(N, U)) :
    (Tensor.PullbackComparison.tensorPullbackComparison f M N).app W
        (Pullback.RestrictedSectionComposition.pullbackSectionValueOn f (Tensor.ProductSheaf.tensorModule M N) U W hW ((Tensor.Bifunctor.tensorBilinear M N).app U m n)) =
      (Tensor.Bifunctor.tensorBilinear ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)).app W
        (Pullback.RestrictedSectionComposition.pullbackSectionValueOn f M U W hW m) (Pullback.RestrictedSectionComposition.pullbackSectionValueOn f N U W hW n) := by
  let e := Tensor.PullbackComparison.tensorPullbackComparison f M N
  let x : Γ((Scheme.Modules.pullback f).obj (Tensor.ProductSheaf.tensorModule M N), f ⁻¹ᵁ U) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (Tensor.ProductSheaf.tensorModule M N)).app U
    ((Tensor.Bifunctor.tensorBilinear M N).app U m n)
  let T := Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
  have he : e.app W (((Scheme.Modules.pullback f).obj (Tensor.ProductSheaf.tensorModule M N)).presheaf.map
      (homOfLE hW).op x) = T.presheaf.map (homOfLE hW).op (e.app (f ⁻¹ᵁ U) x) :=
    ConcreteCategory.congr_hom (e.mapPresheaf.naturality (homOfLE hW).op) x
  change e.app W (((Scheme.Modules.pullback f).obj (Tensor.ProductSheaf.tensorModule M N)).presheaf.map
    (homOfLE hW).op x) = _
  have hp := Tensor.PullbackSectionPairing.tensorPullbackComparison_pairing f M N U m n
  have hn := (Tensor.Bifunctor.tensorBilinear ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)).naturality
    (homOfLE hW) (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U m)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app U n)
  exact he.trans ((congrArg (T.presheaf.map (homOfLE hW).op) hp).trans hn)

variable {X Y Y' P Q : Scheme.{u}} {R : Type u} [CommRing R]
variable (a : P ⟶ X) (b : P ⟶ Y) (d : Q ⟶ P) (j : Y' ⟶ Y) (b' : Q ⟶ Y')
variable (h : d ≫ b = b' ≫ j)
variable (cX : R →+* Γ(X, ⊤)) (cY : R →+* Γ(Y, ⊤))
variable (hc : a.appTop.hom.comp cX = b.appTop.hom.comp cY)
variable (M : X.Modules) (N : Y.Modules)

theorem ambientExternalSectionTensorMap_pullback
    (V : X.Opens) (U : Y.Opens) (U' : Y'.Opens) (W' : Q.Opens)
    (hU : U' ≤ j ⁻¹ᵁ U)
    (hW : W' ≤ d ⁻¹ᵁ (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ U))
    (hM : W' ≤ (d ≫ a) ⁻¹ᵁ V) (hN : W' ≤ b' ⁻¹ᵁ U')
    (n : (Coefficient.ModulePresheaf.coefficientModulePresheaf cY N).obj (.op U))
    (m : (Coefficient.ModulePresheaf.coefficientModulePresheaf cX M).obj (.op V)) :
    (External.SectionRefinement.externalTensorRefinementComparison a b d j b' h M N).app W'
      (Pullback.RestrictedSectionComposition.pullbackSectionValueOn d
        (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N))
        (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ U) W' hW
        (AmbientExternalSectionPairing.ambientExternalSectionTensorMap a b cX cY hc M N V U (n ⊗ₜ[R] m))) =
      (Tensor.Bifunctor.tensorBilinear ((Scheme.Modules.pullback (d ≫ a)).obj M)
        ((Scheme.Modules.pullback b').obj ((Scheme.Modules.pullback j).obj N))).app W'
        (Pullback.RestrictedSectionComposition.pullbackSectionValueOn (d ≫ a) M V W' hM m)
        (Pullback.RestrictedSectionComposition.pullbackSectionValueOn b' ((Scheme.Modules.pullback j).obj N) U' W' hN
          (Pullback.RestrictedSectionComposition.pullbackSectionValueOn j N U U' hU n)) := by
  let Ma := (Scheme.Modules.pullback a).obj M
  let Nb := (Scheme.Modules.pullback b).obj N
  let M' := (Scheme.Modules.pullback (d ≫ a)).obj M
  let N' := (Scheme.Modules.pullback b').obj ((Scheme.Modules.pullback j).obj N)
  let W := a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ U
  let s := Pullback.RestrictedSectionComposition.pullbackSectionValueOn a M V W inf_le_left m
  let t := Pullback.RestrictedSectionComposition.pullbackSectionValueOn b N U W inf_le_right n
  let s' := Pullback.RestrictedSectionComposition.pullbackSectionValueOn d Ma W W' hW s
  let t' := Pullback.RestrictedSectionComposition.pullbackSectionValueOn d Nb W W' hW t
  let eM := (Scheme.Modules.pullbackComp d a).hom.app M
  let eN := (Pullback.SquareMapEquality.modulePullbackSquareIso b b' j d h).hom.app N
  have hm : eM.app W' s' = Pullback.RestrictedSectionComposition.pullbackSectionValueOn (d ≫ a) M V W' hM m :=
    Pullback.RestrictedSectionComposition.pullbackSectionValueOn_comp d a M V W W' inf_le_left hW hM m
  have hn : eN.app W' t' =
      Pullback.RestrictedSectionComposition.pullbackSectionValueOn b' ((Scheme.Modules.pullback j).obj N) U' W' hN
        (Pullback.RestrictedSectionComposition.pullbackSectionValueOn j N U U' hU n) :=
    Pullback.RestrictedSectionComposition.modulePullbackSquareIso_restricted_section b b' j d h N U W U' W'
      inf_le_right hU hW hN n
  have ht := congrArg
    (fun β : Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback d).obj Ma)
      ((Scheme.Modules.pullback d).obj Nb) (Tensor.ProductSheaf.tensorModule M' N') => β.app W' s' t')
    (Tensor.Bifunctor.tensorModuleMap_spec eM eN)
  change (Tensor.Bifunctor.tensorModuleMap eM eN).app W'
      ((Tensor.Bifunctor.tensorBilinear ((Scheme.Modules.pullback d).obj Ma)
        ((Scheme.Modules.pullback d).obj Nb)).app W' s' t') =
    (Tensor.Bifunctor.tensorBilinear M' N').app W' (eM.app W' s') (eN.app W' t') at ht
  rw [hm, hn] at ht
  rw [AmbientExternalSectionPairing.ambientExternalSectionTensorMap_tmul]
  change (Tensor.Bifunctor.tensorModuleMap eM eN).app W'
      ((Tensor.PullbackComparison.tensorPullbackComparison d Ma Nb).app W'
        (Pullback.RestrictedSectionComposition.pullbackSectionValueOn d (Tensor.ProductSheaf.tensorModule Ma Nb) W W' hW ((Tensor.Bifunctor.tensorBilinear Ma Nb).app W s t))) = _
  have hp := tensorPullbackComparison_pairing_on d Ma Nb W W' hW s t
  exact (congrArg
    (fun v : Γ(Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback d).obj Ma)
      ((Scheme.Modules.pullback d).obj Nb), W') => (Tensor.Bifunctor.tensorModuleMap eM eN).app W' v) hp).trans ht

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientExternalPullbackComparison

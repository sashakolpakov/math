import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientExternalPullbackComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.SectionToIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionTensorIsomorphism

/-! # External Affine Frame Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExternalAffineFrameIso

noncomputable section

/-! On two affine frame charts over an affine base, the canonical ambient section pairing is an isomorphism. The proof compares it with the affine-parameter pairing by actual open-pullback section isomorphisms. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

private theorem externalSectionTensorMap_isIso_of_coefficient_eq
    {X Y P : Scheme.{u}} {R : Type u} [CommRing R] (a : P ⟶ X) (b : P ⟶ Y)
    (cX : R →+* Γ(X, ⊤)) (cY cY' : R →+* Γ(Y, ⊤))
    (hc : a.appTop.hom.comp cX = b.appTop.hom.comp cY)
    (hc' : a.appTop.hom.comp cX = b.appTop.hom.comp cY')
    (h : cY = cY') (M : X.Modules) (N : Y.Modules) (V : X.Opens)
    (hi : IsIso (ModuleCat.ofHom (External.SectionTensorMap.externalSectionTensorMap a b cX cY hc M N V))) :
    IsIso (ModuleCat.ofHom (External.SectionTensorMap.externalSectionTensorMap a b cX cY' hc' M N V)) := by
  subst cY'
  exact hi

variable {S X Y P : Scheme.{u}} [IsAffine S]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
variable (H : IsPullback a b f g) (M : X.Modules) (N : Y.Modules)

theorem affineFrames_ambientExternalSectionTensorMap_isIso
    (V : X.Opens) (U : Y.Opens) (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (eV : (Scheme.Modules.pullback V.ι).obj M ≅ Line.Bundles.structureModule V.toScheme)
    (eU : (Scheme.Modules.pullback U.ι).obj N ≅ Line.Bundles.structureModule U.toScheme) :
    IsIso (ModuleCat.ofHom (AmbientExternalSectionPairing.ambientExternalSectionTensorMap a b f.appTop.hom g.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M N V U)) := by
  let d := (b ⁻¹ᵁ U).ι
  let j := U.ι
  let b' := b ∣_ U
  let a' := d ≫ a
  let W := a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ U
  let W' := a' ⁻¹ᵁ V
  let E := Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj N)
  let E' := Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a').obj M)
    ((Scheme.Modules.pullback b').obj ((Scheme.Modules.pullback j).obj N))
  let cP := a.appTop.hom.comp f.appTop.hom
  let cQ := a'.appTop.hom.comp f.appTop.hom
  have hcQ : d.appTop.hom.comp cP = cQ := by ext r; rfl
  have hd : d ≫ b = b' ≫ j := (morphismRestrict_ι b U).symm
  have hlocal : IsPullback a' b' f (j ≫ g) :=
    (isPullback_morphismRestrict b U).flip.paste_horiz H
  have : IsAffine U.toScheme := hU
  have hW' : W' = d ⁻¹ᵁ W := by
    dsimp only [W, W', a', d]
    rw [Scheme.Hom.preimage_inf, (b ⁻¹ᵁ U).ι_preimage_self, inf_top_eq]
    rfl
  have hW : W ≤ d.opensRange := by
    dsimp only [W, d]
    rw [Scheme.Opens.opensRange_ι]
    exact inf_le_right
  let hpre : W' ≤ d ⁻¹ᵁ W := hW'.le
  let C := External.SectionRefinement.externalTensorRefinementComparison a b d j b' hd M N
  have : IsIso C := External.SectionRefinement.externalTensorRefinementComparison_isIso a b d j b' hd M N
  let p := ModuleCat.ofHom (Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen d cP cQ hcQ E W W' hpre)
  have : IsIso p := OpenPullback.SectionToIso.coefficientPullbackSectionToOpen_isIso d cP cQ hcQ E W W' hpre hW hW'
  let eC : (Coefficient.ModulePresheaf.coefficientModulePresheaf cQ ((Scheme.Modules.pullback d).obj E)).obj (op W') ≅
      (Coefficient.ModulePresheaf.coefficientModulePresheaf cQ E').obj (op W') :=
    ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor cQ).mapIso (asIso C)).app (op W')
  let t := asIso p ≪≫ eC
  let s := ((OpenPullback.SectionToIso.coefficientOpenGlobalSectionIso g.appTop.hom N U).toLinearEquiv.rTensor
    ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M).obj (op V))).toModuleIso
  let hcoeff := External.SectionRefinement.externalSection_refinement_coefficients a b d j b' hd
    f.appTop.hom g.appTop.hom (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm
  let γ₀ := ModuleCat.ofHom (External.SectionTensorMap.externalSectionTensorMap a' b' f.appTop.hom
    (j.appTop.hom.comp g.appTop.hom) hcoeff M ((Scheme.Modules.pullback j).obj N) V)
  have hgj : (j ≫ g).appTop.hom = j.appTop.hom.comp g.appTop.hom := by ext r; rfl
  have : IsIso γ₀ := externalSectionTensorMap_isIso_of_coefficient_eq a' b' f.appTop.hom
    (j ≫ g).appTop.hom (j.appTop.hom.comp g.appTop.hom)
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility hlocal).symm hcoeff hgj M
    ((Scheme.Modules.pullback j).obj N) V
    (External.SectionTensorIsomorphism.affineFrame_externalSectionTensorMap_isIso hlocal M
      ((Scheme.Modules.pullback j).obj N) eU V hV eV)
  let γ := asIso γ₀ ≪≫ (Coefficient.PushforwardModuleComparison.coefficientPushforwardModuleComponent a' f.appTop.hom E' V).toModuleIso
  let β := ModuleCat.ofHom (AmbientExternalSectionPairing.ambientExternalSectionTensorMap a b f.appTop.hom g.appTop.hom
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M N V U)
  have hβ : β ≫ t.hom = s.hom ≫ γ.hom := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro n m
    let Nj := (Scheme.Modules.pullback j).obj N
    let Ma := (Scheme.Modules.pullback a').obj M
    let Nb := (Scheme.Modules.pullback b').obj Nj
    let n' := (OpenPullback.SectionToIso.coefficientOpenGlobalSectionIso g.appTop.hom N U).hom n
    let m' : Γ(Ma, W') := ((Scheme.Modules.pullbackPushforwardAdjunction a').unit.app M).app V m
    let βnm := AmbientExternalSectionPairing.ambientExternalSectionTensorMap a b f.appTop.hom g.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M N V U (n ⊗ₜ[Γ(S, ⊤)] m)
    have hn : n' = Pullback.RestrictedSectionComposition.pullbackSectionValueOn j N U ⊤ U.ι_preimage_self.ge n :=
      OpenPullback.SectionToIso.coefficientOpenGlobalSectionIso_apply g.appTop.hom N U n
    have hm : Pullback.RestrictedSectionComposition.pullbackSectionValueOn a' M V W' le_rfl m = m' := by
      change Ma.presheaf.map (𝟙 (op W')) m' = m'
      exact ConcreteCategory.congr_hom (Ma.presheaf.map_id (op W')) m'
    have hp : C.app W' (Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen d cP cQ hcQ E W W' hpre βnm) =
        C.app W' (Pullback.RestrictedSectionComposition.pullbackSectionValueOn d E W W' hpre βnm) :=
      congrArg (fun z : Γ((Scheme.Modules.pullback d).obj E, W') => C.app W' z)
        (Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen_apply d cP cQ hcQ E W W' hpre βnm)
    have ha := AmbientExternalPullbackComparison.ambientExternalSectionTensorMap_pullback a b d j b' hd
      f.appTop.hom g.appTop.hom (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M N
      V U ⊤ W' U.ι_preimage_self.ge hpre le_rfl le_top n m
    have hr : External.SectionTensorMap.externalSectionTensorMap a' b' f.appTop.hom (j.appTop.hom.comp g.appTop.hom)
        hcoeff M Nj V (n' ⊗ₜ[Γ(S, ⊤)] m) =
      (Tensor.Bifunctor.tensorBilinear Ma Nb).app W' m' (Pullback.RestrictedSectionComposition.pullbackSectionValueOn b' Nj ⊤ W' le_top n') :=
      External.SectionTensorMap.externalSectionTensorMap_tmul a' b' f.appTop.hom (j.appTop.hom.comp g.appTop.hom)
        hcoeff M Nj V n' m
    have hr' := hr.trans (congrArg₂ (fun x y => (Tensor.Bifunctor.tensorBilinear Ma Nb).app W' x y) hm.symm
      (congrArg (Pullback.RestrictedSectionComposition.pullbackSectionValueOn b' Nj ⊤ W' le_top) hn))
    change C.app W'
        (Coefficient.PullbackSectionToOpen.coefficientPullbackSectionToOpen d cP cQ hcQ E W W' hpre
          (AmbientExternalSectionPairing.ambientExternalSectionTensorMap a b f.appTop.hom g.appTop.hom
            (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M N V U (n ⊗ₜ[Γ(S, ⊤)] m))) =
      External.SectionTensorMap.externalSectionTensorMap a' b' f.appTop.hom (j.appTop.hom.comp g.appTop.hom)
        hcoeff M ((Scheme.Modules.pullback j).obj N) V
          (n' ⊗ₜ[Γ(S, ⊤)] m)
    exact hp.trans (ha.trans hr'.symm)
  have hs : Function.Bijective s.hom := s.toLinearEquiv.bijective
  have ht : Function.Bijective t.hom := t.toLinearEquiv.bijective
  have hγ : Function.Bijective γ.hom := γ.toLinearEquiv.bijective
  apply (ConcreteCategory.isIso_iff_bijective β).mpr
  constructor
  · intro x y hxy
    apply hs.injective
    apply hγ.injective
    exact (ConcreteCategory.congr_hom hβ x).symm.trans
      ((congrArg t.hom hxy).trans (ConcreteCategory.congr_hom hβ y))
  · intro y
    obtain ⟨v, hv⟩ := hγ.surjective (t.hom y)
    obtain ⟨x, hx⟩ := hs.surjective v
    refine ⟨x, ht.injective ?_⟩
    exact (ConcreteCategory.congr_hom hβ x).trans ((congrArg γ.hom hx).trans hv)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExternalAffineFrameIso

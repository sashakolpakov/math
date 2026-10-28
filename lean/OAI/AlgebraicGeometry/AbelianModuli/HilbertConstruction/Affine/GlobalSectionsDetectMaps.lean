import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModulePresentations

/-! # Global Sections Detect Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GlobalSectionsDetectMaps

noncomputable section

/-! Maps from a quasicoherent module on an affine scheme are determined by their global section maps. Surjectivity on global sections therefore detects epimorphisms with quasicoherent target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem quasicoherent_spec_hom_ext {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] (f g : M ⟶ N)
    (h : moduleSpecΓFunctor.map f = moduleSpecΓFunctor.map g) : f = g := by
  apply (cancel_epi M.fromTildeΓ).mp
  have hf := Scheme.Modules.fromTildeΓNatTrans.naturality f
  have hg := Scheme.Modules.fromTildeΓNatTrans.naturality g
  exact hf.symm.trans ((congrArg (fun a => tilde.map a ≫ N.fromTildeΓ) h).trans hg)

theorem quasicoherent_affine_hom_ext {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] (f g : M ⟶ N) (h : f.app ⊤ = g.app ⊤) : f = g := by
  let F := restrictFunctor X.isoSpec.inv
  have : F.IsEquivalence := Functor.IsEquivalence.mk' _
    (LineBundle.IsoImage.restrictFunctorInverseIso X.isoSpec).symm
    (LineBundle.IsoImage.restrictFunctorInverseIso X.isoSpec.symm)
  apply F.map_injective
  apply quasicoherent_spec_hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have ht : X.isoSpec.inv ''ᵁ ⊤ = ⊤ :=
    X.isoSpec.inv.image_top_eq_opensRange.trans X.isoSpec.inv.opensRange_of_isIso
  have hh : f.app (X.isoSpec.inv ''ᵁ ⊤) = g.app (X.isoSpec.inv ''ᵁ ⊤) := by
    rw [ht]
    exact h
  exact ConcreteCategory.congr_hom hh x

theorem module_epi_of_affine_globalSections_surjective
    {X : Scheme.{u}} [IsAffine X] {M N : X.Modules} [N.IsQuasicoherent]
    (f : M ⟶ N) (hf : Function.Surjective (f.app ⊤)) : Epi f := by
  constructor
  intro P g h hcomp
  apply quasicoherent_affine_hom_ext g h
  apply ConcreteCategory.hom_ext
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact ConcreteCategory.congr_hom (congrArg (fun k : M ⟶ P => k.app ⊤) hcomp) x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GlobalSectionsDetectMaps

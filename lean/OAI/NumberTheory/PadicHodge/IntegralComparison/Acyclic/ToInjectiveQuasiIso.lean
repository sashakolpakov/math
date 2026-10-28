import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ToInjective

/-! # To Injective Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ToInjectiveQuasiIso

noncomputable section

/-! The actual section map from an acyclic resolution to an injective resolution is a quasi-isomorphism. -/

open _root_.CategoryTheory

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C)
  (K : CochainComplex C ℕ) {Z : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)
  [QuasiIso ι] (hK : ∀ a q, Subsingleton (Ext.{z} X (K.X a) (q + 1)))
  (I : InjectiveResolution Z) (φ : K ⟶ I.cocomplex) (hφ : ι ≫ φ = I.ι)

include hφ hK in
theorem homology_isIso (i : ℕ) : IsIso (HomologicalComplex.homologyMap
    (((IntegralComparison.Ext.ModuleFunctor.functor R X 0).mapHomologicalComplex (.up ℕ)).map φ) i) := by
  let a := HomologicalComplex.homologyMap
    (((IntegralComparison.Ext.ModuleFunctor.functor R X 0).mapHomologicalComplex (.up ℕ)).map φ) i
  let e := InjectiveSectionCohomology.homologyIso R X I i
  let : IsIso e.hom := e.isIso_hom
  have h := ToInjective.Comparison.homology R X K ι hK I φ hφ i
  let he : IsIso (a ≫ e.hom) := h.symm ▸ (ToInjective.Comparison.homologyIso R X K ι hK i).isIso_hom
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ a e.hom e.isIso_hom he

include hφ hK in
theorem quasiIso : QuasiIso (((IntegralComparison.Ext.ModuleFunctor.functor R X 0).mapHomologicalComplex (.up ℕ)).map φ) :=
  ⟨fun i => (quasiIsoAt_iff_isIso_homologyMap _ i).mpr (homology_isIso R X K ι hK I φ hφ i)⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ToInjectiveQuasiIso

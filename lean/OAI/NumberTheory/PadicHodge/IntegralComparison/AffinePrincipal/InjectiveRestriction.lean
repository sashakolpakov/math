import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Injective

/-! # Injective Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.InjectiveRestriction

noncomputable section

/-! The injective-resolution comparison commutes with the literal
restriction between two diagrams of opens on the same scheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Injective.Comparison
variable {X : Scheme.{u}} {C : Type u} [Preorder C] [HasFiniteProducts C]
  (G₁ G₂ : C ⥤ X.Opens) (α : G₂ ⟶ G₁)
  {ι : Type u} [LinearOrder ι] (W : ι → C)

def coefficientsMap : Injective.Comparison.coefficients G₁ ⟶ Injective.Comparison.coefficients G₂ where
  app P := Functor.whiskerRight (NatTrans.op α) P.obj
  naturality P Q a := by
    apply NatTrans.ext
    funext r
    exact (a.hom.naturality (α.app r.unop).op).symm

def map (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℕ) :
    (Injective.Comparison.functor G₁ W).obj K ⟶ (Injective.Comparison.functor G₂ W).obj K :=
  AugmentedOrdered.CechForgetNaturality.map W
    ((NatTrans.mapHomologicalComplex (coefficientsMap G₁ G₂ α) (.up ℕ)).app K)

theorem naturality {K L : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℕ}
    (a : K ⟶ L) :
    (Injective.Comparison.functor G₁ W).map a ≫ InjectiveRestriction.map G₁ G₂ α W L =
      InjectiveRestriction.map G₁ G₂ α W K ≫ (Injective.Comparison.functor G₂ W).map a := by
  let T := (AugmentedOrdered.CechFunctor.functor W (D := AddCommGrpCat.{u})).mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (.up ℕ) (.up ℕ) (.up ℕ)
  change T.map _ ≫ T.map _ = T.map _ ≫ T.map _
  rw [← T.map_comp, ← T.map_comp]
  exact congrArg T.map
    ((NatTrans.mapHomologicalComplex (coefficientsMap G₁ G₂ α) (.up ℕ)).naturality a)

variable (N : X.Modules) (c : ℕ)

abbrev sourceMap := InjectiveRestriction.map G₁ G₂ α W ((single _ (.up ℕ) c).obj (Injective.Comparison.sheaf N))
abbrev targetMap := InjectiveRestriction.map G₁ G₂ α W (ShiftedOpenInjectiveResolution.complex (Injective.Comparison.sheaf N) c)

theorem comparison_square : Injective.Comparison.comparison G₁ W N c ≫ targetMap G₁ G₂ α W N c =
    sourceMap G₁ G₂ α W N c ≫ Injective.Comparison.comparison G₂ W N c :=
  InjectiveRestriction.naturality G₁ G₂ α W (ShiftedOpenInjectiveResolution.augmentation (Injective.Comparison.sheaf N) c)

theorem homology_square [N.IsQuasicoherent]
    (h₁ : ∀ r, IsAffineOpen (G₁.obj r)) (h₂ : ∀ r, IsAffineOpen (G₂.obj r)) (q : ℕ) :
    (Injective.Comparison.homologyIso G₁ W N c h₁ q).hom ≫ homologyMap (targetMap G₁ G₂ α W N c) q =
      homologyMap (sourceMap G₁ G₂ α W N c) q ≫ (Injective.Comparison.homologyIso G₂ W N c h₂ q).hom := by
  change homologyMap (Injective.Comparison.comparison G₁ W N c) q ≫ homologyMap _ q =
    homologyMap _ q ≫ homologyMap (Injective.Comparison.comparison G₂ W N c) q
  rw [← homologyMap_comp, ← homologyMap_comp, comparison_square]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.InjectiveRestriction

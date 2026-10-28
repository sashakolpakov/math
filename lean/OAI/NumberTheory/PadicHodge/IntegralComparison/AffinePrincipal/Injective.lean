import OAI.NumberTheory.PadicHodge.IntegralComparison.ShiftedOpenInjectiveResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.AugmentedCechQuasiIso
import OAI.AlgebraicGeometry.SheafCohomology.AffineVanishing
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdditiveSections

/-! # Injective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Injective.Comparison

noncomputable section

/-! Affine principal Cech cohomology of the original single module is
identified through its actual augmentation with a shifted injective
resolution. The comparison commutes with coefficient endomorphisms. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {C : Type u} [Preorder C] [HasFiniteProducts C]
  (G : C ⥤ X.Opens) {ι : Type u} [LinearOrder ι] (W : ι → C)

abbrev sheaf (N : X.Modules) := (SheafOfModules.toSheaf X.ringCatSheaf).obj N

def coefficients : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
    Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (Functor.whiskeringLeft Cᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj G.op

instance coefficients_additive : (coefficients G).Additive where
  map_add := rfl

def functor : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℕ ⥤
    CochainComplex AddCommGrpCat.{u} ℕ :=
  (coefficients G).mapHomologicalComplex (.up ℕ) ⋙
    (AugmentedOrdered.CechFunctor.functor W).mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (.up ℕ) (.up ℕ) (.up ℕ)

variable (N : X.Modules) (c : ℕ)

abbrev source := (functor G W).obj ((single _ (.up ℕ) c).obj (sheaf N))
abbrev target := (functor G W).obj (ShiftedOpenInjectiveResolution.complex (sheaf N) c)

def comparison : source G W N c ⟶ target G W N c :=
  (functor G W).map (ShiftedOpenInjectiveResolution.augmentation (sheaf N) c)

omit [Preorder C] [HasFiniteProducts C] [LinearOrder ι] in
theorem affine_acyclic [N.IsQuasicoherent] (V : X.Opens) (hV : IsAffineOpen V) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((AlgebraicGeometry.SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat V.isOpenEmbedding).obj (sheaf N)) (q+1)) := by
  let : IsAffine V.toScheme := hV
  change Subsingleton (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H (N.restrict V.ι) (q+1))
  exact AlgebraicGeometry.SheafCohomology.AffineVanishing.Projective.moduleAffineHSucc_subsingleton (N.restrict V.ι) q

theorem quasiIso [N.IsQuasicoherent] (hG : ∀ r, IsAffineOpen (G.obj r)) :
    QuasiIso (comparison G W N c) := by
  change QuasiIso (AugmentedOrdered.CechForgetNaturality.map W
    (((coefficients G).mapHomologicalComplex (.up ℕ)).map
      (ShiftedOpenInjectiveResolution.augmentation (sheaf N) c)))
  apply IntegralComparison.Additive.AugmentedCechQuasiIso.quasiIso_of_evaluation
  intro p a
  change QuasiIso
    (((Acyclic.OpenInjectiveResolution.sections
      (G.obj ((AugmentedOrdered.Cech.formal W p).obj a))).mapHomologicalComplex (.up ℕ)).map
        (ShiftedOpenInjectiveResolution.augmentation (sheaf N) c))
  exact ShiftedOpenInjectiveResolution.sections_quasiIso (sheaf N) c _
    (fun q => affine_acyclic N _ (hG _) q)

variable {P : X.Modules} (f : N ⟶ P)

def sourceMap : source G W N c ⟶ source G W P c :=
  (functor G W).map ((single _ (.up ℕ) c).map ((SheafOfModules.toSheaf X.ringCatSheaf).map f))

def targetMap : target G W N c ⟶ target G W P c :=
  (functor G W).map (ShiftedOpenInjectiveResolution.map (sheaf N) c
    ((SheafOfModules.toSheaf X.ringCatSheaf).map f))

theorem naturality : comparison G W N c ≫ targetMap G W N c f =
    sourceMap G W N c f ≫ comparison G W P c := by
  change (functor G W).map _ ≫ (functor G W).map _ =
    (functor G W).map _ ≫ (functor G W).map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ShiftedOpenInjectiveResolution.naturality]

def homologyIso [N.IsQuasicoherent] (hG : ∀ r, IsAffineOpen (G.obj r)) (q : ℕ) :
    (source G W N c).homology q ≅ (target G W N c).homology q :=
  let := quasiIso G W N c hG
  isoOfQuasiIsoAt (comparison G W N c) q

theorem homology_naturality [N.IsQuasicoherent] [P.IsQuasicoherent]
    (hG : ∀ r, IsAffineOpen (G.obj r)) (q : ℕ) :
    (homologyIso G W N c hG q).hom ≫ homologyMap (targetMap G W N c f) q =
      homologyMap (sourceMap G W N c f) q ≫ (homologyIso G W P c hG q).hom := by
  change homologyMap (comparison G W N c) q ≫ homologyMap _ q =
    homologyMap _ q ≫ homologyMap (comparison G W P c) q
  rw [← homologyMap_comp, ← homologyMap_comp, naturality]

theorem fixed_iff [N.IsQuasicoherent] (hG : ∀ r, IsAffineOpen (G.obj r))
    (a : N ⟶ N) (q : ℕ) (x : (source G W N c).homology q) :
    homologyMap (targetMap G W N c a) q ((homologyIso G W N c hG q).hom x) =
        (homologyIso G W N c hG q).hom x ↔
      homologyMap (sourceMap G W N c a) q x = x := by
  have hn := ConcreteCategory.congr_hom (homology_naturality G W N c a hG q) x
  change homologyMap (targetMap G W N c a) q ((homologyIso G W N c hG q).hom x) =
    (homologyIso G W N c hG q).hom (homologyMap (sourceMap G W N c a) q x) at hn
  rw [hn]
  exact (ConcreteCategory.bijective_of_isIso (homologyIso G W N c hG q).hom).injective.eq_iff

variable (U : X.Opens) (hU : IsAffineOpen U)
  {κ : Type u} [LinearOrder κ] (V : κ → IntegralComparison.Principal.SectionPresheaf.Index U)

theorem principal_quasiIso [N.IsQuasicoherent] :
    QuasiIso (comparison (IntegralComparison.Principal.AdditiveSections.opens U hU) V N c) :=
  quasiIso (IntegralComparison.Principal.AdditiveSections.opens U hU) V N c (fun r => hU.basicOpen r.val)

def principalHomologyIso [N.IsQuasicoherent] (q : ℕ) :=
  homologyIso (IntegralComparison.Principal.AdditiveSections.opens U hU) V N c (fun r => hU.basicOpen r.val) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Injective.Comparison

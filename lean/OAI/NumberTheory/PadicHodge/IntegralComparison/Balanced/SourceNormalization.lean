import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.SourceNaturality

/-! # Source Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SourceNormalization

noncomputable section

/-! The genuine balanced mixed-resolution comparison is normalized by
its source augmentation for every intermediate coefficient complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z t
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C]
  (P : ChainComplex C ℕ) {Z : C} (ε : P ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ε]
  {Y : C} (I : InjectiveResolution Y) (K : CochainComplex C ℕ) (g : K ⟶ I.cocomplex)

local instance coproducts : HasCoproducts.{0} (ModuleCat.{z} R) :=
  fun T => (ModuleCat.hasColimitsOfSize.{z,t,0,0} R).has_colimits_of_shape (Discrete T)

def comparison (i : ℕ) :=
  HomologicalComplex.homologyMap (ResolutionHom.SourceNaturality.totalMap R P g) i ≫
    (ResolutionHom.Total.homologyIso R P ε I i).hom

private theorem normalization {A : Type*} [Category A]
    {U V U' V' E : A} (a : U ⟶ V) (s : U ⟶ U') (m : V ⟶ V')
    (e : U' ≅ V') (h : U' ⟶ E) (w : a ≫ m = s ≫ e.hom) :
    a ≫ (m ≫ e.inv ≫ h) = s ≫ h := by
  rw [← Category.assoc a m, w]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

theorem source_edge (i : ℕ) :
    HomologicalComplex.homologyMap (ResolutionHom.Total.edge R P ε K) i ≫
      comparison R P ε I K g i =
    HomologicalComplex.homologyMap (ResolutionHom.SourceNaturality.sectionsMap R (Z := Z) g) i ≫
      (InjectiveSectionCohomology.homologyIso R Z I i).hom := by
  let e := ResolutionHom.Total.edge R P ε I.cocomplex
  let : QuasiIso e := ResolutionHom.Total.edge_quasiIso R P ε I.cocomplex I.injective
  have h := (HomologicalComplex.homologyMap_comp (ResolutionHom.Total.edge R P ε K)
    (ResolutionHom.SourceNaturality.totalMap R P g) i).symm.trans
      ((congrArg (fun a => HomologicalComplex.homologyMap a i)
        (ResolutionHom.SourceNaturality.square R P ε g)).trans
          (HomologicalComplex.homologyMap_comp
            (ResolutionHom.SourceNaturality.sectionsMap R (Z := Z) g) e i))
  exact normalization _ _ _ (isoOfQuasiIsoAt e i)
    (InjectiveSectionCohomology.homologyIso R Z I i).hom h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SourceNormalization

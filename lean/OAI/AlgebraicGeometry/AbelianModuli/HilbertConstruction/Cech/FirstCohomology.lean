import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ResolutionFirstCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafResolution
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.GroupProductCoordinates
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # First Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.FirstCohomology.IntrinsicCech

noncomputable section

/-! The first-cohomology criterion applied to the actual sheaf Cech resolution. For a finite cover, lower-degree vanishing can be checked on the restriction-pushforward factors. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u

variable {X : TopCat.{u}}

theorem sheafCohomology_finiteProduct_vanish
    {ι : Type u} [Finite ι] (F : ι → X.Sheaf AddCommGrpCat.{u}) (n : ℕ)
    (hF : ∀ i, Subsingleton (CategoryTheory.Sheaf.H (F i) n)) :
    Subsingleton (CategoryTheory.Sheaf.H (∏ᶜ F) n) := by
  let : Fintype ι := Fintype.ofFinite ι
  let T := CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n
  let e : T.obj (∏ᶜ F) ≅ AddCommGrpCat.of (∀ i, T.obj (F i)) :=
    PreservesProduct.iso T F ≪≫ HilbertConstruction.Additive.GroupProductCoordinates.IntrinsicCech.productIsoPi (fun i => T.obj (F i))
  have hi : Function.Injective e.hom :=
    (AddCommGrpCat.mono_iff_injective e.hom).mp inferInstance
  change Subsingleton (T.obj (∏ᶜ F))
  refine subsingleton_of_forall_eq 0 fun x => ?_
  apply hi
  funext i
  exact (hF i).elim _ _

private def cechSheafSiteEquivalence (X : TopCat.{u}) :
    X.Sheaf AddCommGrpCat.{u} ≌
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} where
  functor := { obj F := F, map a := a }
  inverse := { obj F := F, map a := a }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

private instance (X : TopCat.{u}) : (cechSheafSiteEquivalence X).functor.Additive where
  map_add := by intros; rfl

variable (F : X.Sheaf AddCommGrpCat.{u})
  {ι : Type u} (U : ι → Opens X)

theorem cech_firstCohomology_vanish
    (hU : iSup U = ⊤) (n : ℕ)
    (hF : ∀ p r, r < n + 1 → Subsingleton (CategoryTheory.Sheaf.H (IntrinsicCech.SheafTerms.cechTerm F U p) r))
    (hd : Function.Injective (CategoryTheory.Sheaf.H.map (SheafDifferential.IntrinsicCech.cechDifferential F U 0) (n + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  let T := (cechSheafSiteEquivalence X).functor
  let K := (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj (IntrinsicCech.SheafComplex.cechComplex F U)
  let e : T.obj F ⟶ K.X 0 := T.map (SheafAugmentation.IntrinsicCech.cechAugmentation F U)
  have : Mono (SheafAugmentation.IntrinsicCech.cechAugmentation F U) := SheafResolution.IntrinsicCech.cechAugmentation_mono F U hU
  have : Mono e := by
    change Mono (T.map (SheafAugmentation.IntrinsicCech.cechAugmentation F U))
    infer_instance
  have hdK (p : ℕ) : K.d p (p + 1) = T.map (SheafDifferential.IntrinsicCech.cechDifferential F U p) :=
    congrArg (fun z => T.map z) (IntrinsicCech.SheafComplex.cechComplex_d F U p)
  have w : e ≫ K.d 0 1 = 0 := by
    rw [hdK 0]
    exact (T.map_comp (SheafAugmentation.IntrinsicCech.cechAugmentation F U) (SheafDifferential.IntrinsicCech.cechDifferential F U 0)).symm.trans
      ((congrArg (fun z => T.map z) (SheafAugmentation.IntrinsicCech.cechAugmentation_comp F U)).trans (T.map_zero _ _))
  apply ResolutionFirstCohomology.IntrinsicCech.resolution_firstCohomology_vanish_of_first_differential_injective
    K e w
  · let E : (SheafAugmentation.IntrinsicCech.cechAugmentedShortComplex F U).map T ≅ ShortComplex.mk e (K.d 0 1) w :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by exact (Category.id_comp e).trans (Category.comp_id e).symm)
        (by exact (Category.id_comp _).trans ((hdK 0).trans (Category.comp_id _).symm))
    exact ShortComplex.exact_of_iso E ((ZeroCycleStalks.IntrinsicCech.cechAugmentedShortComplex_exact F U hU).map T)
  · intro p
    let S := ShortComplex.mk (SheafDifferential.IntrinsicCech.cechDifferential F U p) (SheafDifferential.IntrinsicCech.cechDifferential F U (p + 1))
      (IntrinsicCech.SheafComplex.cechDifferential_comp F U p)
    have hS : S.Exact := PositiveCycleStalks.IntrinsicCech.cechShortComplex_exact F U hU p
    let E : S.map T ≅ AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K p :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by exact (Category.id_comp _).trans ((hdK p).trans (Category.comp_id _).symm))
        (by exact (Category.id_comp _).trans ((hdK (p + 1)).trans (Category.comp_id _).symm))
    exact ShortComplex.exact_of_iso E (hS.map T)
  · exact hF
  · rw [hdK 0]
    exact hd

theorem cech_firstCohomology_vanish_of_factors [Finite ι]
    (hU : iSup U = ⊤) (n : ℕ)
    (hF : ∀ (p r : ℕ), r < n + 1 → ∀ i : Fin (p + 1) → ι,
      Subsingleton (CategoryTheory.Sheaf.H (IntrinsicCech.SheafTerms.cechTermFactor F U p i) r))
    (hd : Function.Injective (CategoryTheory.Sheaf.H.map (SheafDifferential.IntrinsicCech.cechDifferential F U 0) (n + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  apply cech_firstCohomology_vanish F U hU n _ hd
  intro p r hr
  exact sheafCohomology_finiteProduct_vanish (IntrinsicCech.SheafTerms.cechTermFactor F U p) r (hF p r hr)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.FirstCohomology.IntrinsicCech

import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.OpenSectionsExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Functor Additive -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.FunctorAdditive

noncomputable section

section

/-! The native Čech complex preserves a short exact sequence whose first sheaf is acyclic on intersections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)

local instance : (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor (X := X) U).PreservesZeroMorphisms :=
  SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor_preservesZeroMorphisms (X := X) U

theorem cechCochainFunctor_mono {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : F ⟶ G) [Mono f] (p : ℕ) : Mono ((SheafCohomology.Cech.CochainExact.TopCat.Sheaf.cechCochainFunctor (X := X) U p).map f) := by
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  intro x y h
  apply (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U p).injective
  funext t
  have he := congrArg (fun z => SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv G.obj U p z t) h
  rw [SheafCohomology.Cech.CochainExact.TopCat.Sheaf.cechCochainFunctor_map_apply, SheafCohomology.Cech.CochainExact.TopCat.Sheaf.cechCochainFunctor_map_apply] at he
  let E := (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op (∏ᶜ fun k : Fin (p + 1) => U (t k)))
  have hF : Mono ((TopCat.Sheaf.forget AddCommGrpCat.{0} X).map f) := inferInstance
  let : Mono f.hom := hF
  have hm : Mono (E.map f.hom) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).mp hm he

theorem cechCochainFunctor_surjective {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : F ⟶ G) (p : ℕ)
    (hf : ∀ t : Fin (p + 1) → ι,
      Function.Surjective (f.hom.app (op (∏ᶜ fun k : Fin (p + 1) => U (t k))))) :
    Function.Surjective ((SheafCohomology.Cech.CochainExact.TopCat.Sheaf.cechCochainFunctor (X := X) U p).map f) := by
  intro z
  choose y hy using fun t => hf t (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv G.obj U p z t)
  let y' := (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U p).symm y
  refine ⟨y', ?_⟩
  apply (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv G.obj U p).injective
  funext t
  have hm := SheafCohomology.Cech.CochainExact.TopCat.Sheaf.cechCochainFunctor_map_apply U f p y' t
  have he := congrFun ((SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U p).apply_symm_apply y) t
  exact hm.trans ((congrArg (f.hom.app (op (∏ᶜ fun k : Fin (p + 1) => U (t k)))) he).trans (hy t))

theorem cechCochainFunctor_shortExact
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)) (hS : S.ShortExact)
    (h₁ : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U S.X₁) (p : ℕ) :
    (S.map (SheafCohomology.Cech.CochainExact.TopCat.Sheaf.cechCochainFunctor (X := X) U p)).ShortExact := by
  let : Mono S.f := hS.mono_f
  have hm : Mono ((SheafCohomology.Cech.CochainExact.TopCat.Sheaf.cechCochainFunctor (X := X) U p).map S.f) := cechCochainFunctor_mono U S.f p
  have he : Epi ((SheafCohomology.Cech.CochainExact.TopCat.Sheaf.cechCochainFunctor (X := X) U p).map S.g) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (cechCochainFunctor_surjective U S.g p
      (fun t => Betti.Sheaf.OpenSectionsExact.Cech.sheafOpenSections_surjective S hS _ (h₁ p t 0)))
  have hx := SheafCohomology.Cech.CochainExact.TopCat.Sheaf.cechCochainFunctor_exact_of_sections U S p
    (fun t x hx => Betti.Sheaf.OpenSectionsExact.Cech.sheafOpenSections_exact S hS _ x hx)
  exact { exact := hx, mono_f := hm, epi_g := he }

theorem cechSheafComplexFunctor_shortExact
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)) (hS : S.ShortExact)
    (h₁ : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U S.X₁) :
    (@ShortComplex.map _ _ _ _ _ _ S (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor (X := X) U)
      (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor_preservesZeroMorphisms (X := X) U)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro p
  exact cechCochainFunctor_shortExact U S hS h₁ p

end

/-! The actual native Čech functors preserve addition of coefficient maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

theorem additivePiMap_add {ι : Type} (F G : ι → AddCommGrpCat.{0})
    (f g : ∀ i, F i ⟶ G i) :
    CategoryTheory.Limits.Pi.map (fun i => f i + g i) = CategoryTheory.Limits.Pi.map f + CategoryTheory.Limits.Pi.map g := by
  apply CategoryTheory.Limits.Pi.hom_ext
  intro i
  rw [CategoryTheory.Limits.Pi.map_π, Preadditive.add_comp, CategoryTheory.Limits.Pi.map_π, CategoryTheory.Limits.Pi.map_π, Preadditive.comp_add]

instance nativeCechFunctor_additive {X : Type} [TopologicalSpace X] {ι : Type} (U : ι → Opens X) :
    (cechComplexFunctor (A := AddCommGrpCat.{0}) U).Additive where
  map_add := by
    intro F G f g
    apply HomologicalComplex.Hom.ext
    funext p
    change CategoryTheory.Limits.Pi.map (fun t : Fin (p + 1) → ι => f.app (op (∏ᶜ fun k => U (t k))) +
        g.app (op (∏ᶜ fun k => U (t k)))) = _
    exact additivePiMap_add _ _ _ _

instance nativeSheafCechFunctor_additive {X : TopCat.{0}} {ι : Type} (U : ι → Opens X) :
    (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor (X := X) U).Additive := by
  change (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} ⋙
    cechComplexFunctor (A := AddCommGrpCat.{0}) U).Additive
  infer_instance

end

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.FunctorAdditive

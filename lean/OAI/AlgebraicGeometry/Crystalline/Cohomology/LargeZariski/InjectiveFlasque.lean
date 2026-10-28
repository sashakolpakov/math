import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.Colimits
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.ShrinkYoneda
import Mathlib.Topology.Sheaves.Flasque

/-! # Injective Flasque -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.InjectiveFlasque.LargeZariskiInjectiveFlasque

noncomputable section

/-!
# Injective native-size module sheaves extend sections across opens

Free module sheaves representing sections turn an inclusion of opens
into a monomorphism. Injectivity supplies every section extension.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

universe u

variable (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})

def representable (U : X.Opens) : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R) :=
  (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)).obj
    (shrinkYoneda.{u + 1}.obj U ⋙ ModuleCat.free R)

def map {U V : X.Opens} (i : U ⟶ V) : representable R X U ⟶ representable R X V :=
  (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)).map
    (Functor.whiskerRight (shrinkYoneda.{u + 1}.map i) (ModuleCat.free R))

def homEquiv {U : X.Opens}
    {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)} :
    (representable R X U ⟶ F) ≃ F.obj.obj (op U) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)).homEquiv _ _).trans
    ((((ModuleCat.adj R).whiskerRight X.Opensᵒᵖ).homEquiv _ _).trans shrinkYonedaEquiv)

theorem map_mono {U V : X.Opens} (i : U ⟶ V) : Mono (LargeZariskiInjectiveFlasque.map R X i) := by
  have : ∀ T, Mono ((Functor.whiskerRight (shrinkYoneda.{u + 1}.map i) (ModuleCat.free R)).app T) := by
    intro T
    apply (ModuleCat.mono_iff_injective _).mpr
    exact Finsupp.mapDomain_injective
      (fun _a _b _ => shrinkYonedaObjObjEquiv.injective (Subsingleton.elim _ _))
  have : Mono (Functor.whiskerRight (shrinkYoneda.{u + 1}.map i) (ModuleCat.free R)) := by
    exact NatTrans.mono_of_mono_app _
  exact Functor.map_mono
    (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)) _

theorem homEquiv_map {U V : X.Opens} (i : U ⟶ V)
    {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)}
    (f : representable R X V ⟶ F) :
    LargeZariskiInjectiveFlasque.homEquiv R X (LargeZariskiInjectiveFlasque.map R X i ≫ f) = F.obj.map i.op (LargeZariskiInjectiveFlasque.homEquiv R X f) := by
  let a₁ := sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)
  let a₂ := (ModuleCat.adj R).whiskerRight X.Opensᵒᵖ
  let α := Functor.whiskerRight (shrinkYoneda.{u + 1}.map i) (ModuleCat.free R)
  have h₁ := a₁.homEquiv_naturality_left α f
  have h₂ := a₂.homEquiv_naturality_left (shrinkYoneda.{u + 1}.map i) (a₁.homEquiv _ _ f)
  change shrinkYonedaEquiv (a₂.homEquiv _ _ (a₁.homEquiv _ _
    ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)).map α ≫ f))) =
      F.obj.map i.op (shrinkYonedaEquiv (a₂.homEquiv _ _ (a₁.homEquiv _ _ f)))
  exact (congrArg (fun h => shrinkYonedaEquiv (a₂.homEquiv _ _ h)) h₁).trans
    ((congrArg (fun h => shrinkYonedaEquiv h) h₂).trans
      (shrinkYonedaEquiv_naturality _ _).symm)

theorem flasque (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)) [Injective F] :
    TopCat.Sheaf.IsFlasque F := by
  constructor
  intro U V i
  rw [ModuleCat.epi_iff_surjective]
  intro s
  let g : representable R X V.unop ⟶ F := (LargeZariskiInjectiveFlasque.homEquiv R X).symm s
  let m : representable R X V.unop ⟶ representable R X U.unop := LargeZariskiInjectiveFlasque.map R X i.unop
  have : Mono m := LargeZariskiInjectiveFlasque.map_mono R X i.unop
  let h : representable R X U.unop ⟶ F := Injective.factorThru g m
  refine ⟨LargeZariskiInjectiveFlasque.homEquiv R X h, ?_⟩
  have hnat : F.obj.map i (LargeZariskiInjectiveFlasque.homEquiv R X h) = LargeZariskiInjectiveFlasque.homEquiv R X (m ≫ h) := by
    simpa only [m, Quiver.Hom.op_unop, Opposite.op_unop] using (homEquiv_map R X i.unop h).symm
  rw [hnat, Injective.comp_factorThru]
  exact (LargeZariskiInjectiveFlasque.homEquiv R X).apply_symm_apply s

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.InjectiveFlasque.LargeZariskiInjectiveFlasque

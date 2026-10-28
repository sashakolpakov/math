import OAI.AlgebraicGeometry.SheafCohomology.Cech
import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComparisonNaturality

/-! # Cech Scalars -/

namespace OAI.AlgebraicGeometry.SheafCohomology.CechScalars

noncomputable section

open _root_.TopCat

/-! The canonical action of global regular functions on native Čech cohomology. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

namespace TopCat.Sheaf
open _root_.TopCat.Sheaf

instance cechComplexFunctor_additive {X : TopCat.{u}} {ι : Type u}
    (U : ι → Opens X) : (cechComplexFunctor (A := AddCommGrpCat.{u}) U).Additive where
  map_add := by
    intro F G f g
    apply HomologicalComplex.Hom.ext
    funext n
    change Limits.Pi.map (fun i : Fin (n + 1) → ι =>
      (f + g).app (Opposite.op (∏ᶜ fun k : Fin (n + 1) => U (i k)))) =
      Limits.Pi.map (fun i : Fin (n + 1) → ι =>
        f.app (Opposite.op (∏ᶜ fun k : Fin (n + 1) => U (i k)))) +
      Limits.Pi.map (fun i : Fin (n + 1) → ι =>
        g.app (Opposite.op (∏ᶜ fun k : Fin (n + 1) => U (i k))))
    apply Pi.hom_ext
    intro i
    rw [Pi.map_π, Preadditive.add_comp, Pi.map_π, Pi.map_π]
    exact Preadditive.comp_add _ _ _ _ _ _

end TopCat.Sheaf

namespace Projective

/-- Native Čech cohomology, functorially in the actual scheme module. -/
def moduleCechCohomologyFunctor {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) : X.Modules ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf ⋙
    CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    cechComplexFunctor U ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) n

instance moduleCechCohomologyFunctor_additive {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) : (moduleCechCohomologyFunctor U n).Additive := by
  let S := SheafOfModules.toSheaf X.ringCatSheaf
  let P := CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let C := cechComplexFunctor (A := AddCommGrpCat.{u}) U
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) n
  have : C.Additive := CechScalars.TopCat.Sheaf.cechComplexFunctor_additive (X := TopCat.of X) U
  constructor
  intro M N f g
  change H.map (C.map (P.map (S.map (f + g)))) =
    H.map (C.map (P.map (S.map f))) + H.map (C.map (P.map (S.map g)))
  rw [S.map_add, P.map_add, C.map_add, H.map_add]

/-- Global functions act by applying native Čech cohomology to their actual
endomorphisms of the coefficient module. -/
def cechGlobalFunctionsAction {X : Scheme.{u}} (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    Γ(X, ⊤) →+* End ((moduleCechCohomologyFunctor U n).obj M) where
  toFun r := (moduleCechCohomologyFunctor U n).map (AffineH.Projective.globalSmulEndRingHom M r)
  map_zero' := by rw [map_zero, Functor.map_zero]
  map_one' := by
    rw [map_one]
    exact (moduleCechCohomologyFunctor U n).map_id M
  map_add' r s := by rw [map_add, Functor.map_add]
  map_mul' r s := by
    rw [map_mul]
    exact (moduleCechCohomologyFunctor U n).map_comp
      (AffineH.Projective.globalSmulEndRingHom M s) (AffineH.Projective.globalSmulEndRingHom M r)

/-- The canonical module structure on native Čech cohomology. -/
@[instance_reducible]
def cechGlobalFunctionsModule {X : Scheme.{u}} (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    Module Γ(X, ⊤) ((moduleCechCohomologyFunctor U n).obj M) := by
  change Module Γ(X, ⊤) (ModuleCat.mkOfSMul' (cechGlobalFunctionsAction M U n))
  infer_instance

/-- The scalar action is the cohomology map induced by actual sectionwise multiplication. -/
theorem cechGlobalFunctionsModule_smul {X : Scheme.{u}} (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) (r : Γ(X, ⊤))
    (x : (moduleCechCohomologyFunctor U n).obj M) :
    letI := cechGlobalFunctionsModule M U n
    r • x = (moduleCechCohomologyFunctor U n).map (AffineH.Projective.globalSmulHom M r) x := rfl

/-- The actual complex base map gives the canonical complex Čech module structure. -/
@[instance_reducible]
def cechComplexCohomologyModule (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (M : A.carrier.Modules)
    {ι : Type} (U : ι → A.carrier.Opens) (n : ℕ) :
    Module ℂ ((moduleCechCohomologyFunctor U n).obj M) := by
  letI := cechGlobalFunctionsModule M U n
  exact Module.compHom _ (Sheaves.Projective.complexGlobalScalars A)

end Projective

end

end OAI.AlgebraicGeometry.SheafCohomology.CechScalars

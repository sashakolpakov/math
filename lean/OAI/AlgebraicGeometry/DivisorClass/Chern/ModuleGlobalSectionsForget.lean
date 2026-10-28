import OAI.AlgebraicGeometry.DivisorClass.Chern.ModuleSheafificationForget
import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.GammaAugmentation

/-! # Module Global Sections Forget -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ModuleGlobalSectionsForget

noncomputable section

/-! Actual module global sections and singular sheafification after forgetting scalars. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [Ring R] (X : TopCat.{0})

def moduleForgetGlobalSectionsIso (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (ModuleSheafificationForget.moduleForgetSheafComplex R X K) ≅
      ((forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℕ)).obj
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex (⊤ : Opens X) K) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j _
    change (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}).map ((K.d i j).hom.app (op (⊤ : Opens X))) ≫ 𝟙 _ =
      𝟙 _ ≫ (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}).map ((K.d i j).hom.app (op (⊤ : Opens X)))
    rw [Category.comp_id, Category.id_comp])

def moduleSingularToAbelianSections (A : ModuleCat.{0} R) :
    ((forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℕ)).obj (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains A X) ⟶
      CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (ModuleSheafificationForget.moduleForgetSheafComplex R X (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex A X))) :=
  ((forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℕ)).map
      (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections A X) ≫
    (moduleForgetGlobalSectionsIso R X (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex A X))).inv

theorem moduleSingularToAbelianSections_apply (A : ModuleCat.{0} R) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains A X).X n) :
    (moduleSingularToAbelianSections R X A).f n c = (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections A X).f n c := rfl

theorem rationalSingularToGamma_eq_sections :
    Singular.GammaAugmentation.rationalSingularToGamma X ≫ (GammaSectionsComparison.abelianGammaSectionsIso (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)).hom =
      moduleSingularToAbelianSections ℚ X (ModuleCat.of ℚ ℚ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  exact Singular.GammaAugmentation.rationalSingularToGamma_top X n c

def complexForgetHomologyIso (K : CochainComplex (ModuleCat.{0} ℂ) ℕ) (n : ℕ) :
    ((Complex.SheafForget.complexModuleForget.mapHomologicalComplex (.up ℕ)).obj K).homology n ≅ Complex.SheafForget.complexModuleForget.obj (K.homology n) :=
  (K.sc n).mapHomologyIso Complex.SheafForget.complexModuleForget

theorem complexForgetHomologyIso_naturality
    {K L : CochainComplex (ModuleCat.{0} ℂ) ℕ} (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap ((Complex.SheafForget.complexModuleForget.mapHomologicalComplex (.up ℕ)).map f) n ≫
      (complexForgetHomologyIso L n).hom = (complexForgetHomologyIso K n).hom ≫
        Complex.SheafForget.complexModuleForget.map (HomologicalComplex.homologyMap f n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f) Complex.SheafForget.complexModuleForget

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ModuleGlobalSectionsForget

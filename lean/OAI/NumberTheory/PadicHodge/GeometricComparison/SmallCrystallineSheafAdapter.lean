import OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineTopologyAdapter

/-! # Small Crystalline Sheaf Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineSheafAdapter.SmallCrystallineAdapter

noncomputable section

/-! Exact transport of the structure and coefficient sheaves on the equivalent small crystalline sites. -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry Opposite

universe u
variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
  {X : Over (Spec (CommRingCat.of k))}

abbrev W := WittVector p k
abbrev Coeff := ULift.{u + 1} (W (p := p) (k := k))

abbrev presheaf65 := IntegralComparison.Crystalline.Site.AffineThickening.structureModulePresheaf (p := p)
  (δB := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (f := IntegralComparison.Witt.Crystalline.wittStructureMap p k X)

def ambientModuleEquiv (S : SmallCrystallineDpow.SmallCrystallineAdapter.Small62 (p := p) (k := k) (X := X)) :
    (presheaf65 (p := p) (k := k) (X := X)).obj (op (SmallCrystallineDpow.SmallCrystallineAdapter.to65Object S)) ≃ₗ[W (p := p) (k := k)]
      (AlgebraicGeometry.Crystalline.Cohomology.Site.functions p k X).obj (op S) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' b x := by
    change S.thickening.ring at x
    change algebraMap (WittVector p k) S.thickening.ring b * x = b • x
    exact (Algebra.smul_def b x).symm

def presheafIso : SmallCrystallineDpow.SmallCrystallineAdapter.to65.op ⋙ presheaf65 (p := p) (k := k) (X := X) ≅
    AlgebraicGeometry.Crystalline.Cohomology.Site.functions p k X :=
  NatIso.ofComponents (fun S => (ambientModuleEquiv S.unop).toModuleIso)
    (fun f => by apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl)

abbrev largePresheaf65 := IntegralComparison.Crystalline.Site.AffineThickening.structureModulePresheafLarge (p := p)
  (δB := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (f := IntegralComparison.Witt.Crystalline.wittStructureMap p k X)

def largePresheafIso : SmallCrystallineDpow.SmallCrystallineAdapter.to65.op ⋙ largePresheaf65 (p := p) (k := k) (X := X) ≅
    AlgebraicGeometry.Crystalline.Cohomology.Site.functionsLarge p k X :=
  isoWhiskerRight presheafIso
    (ModuleCat.uliftFunctor.{u + 1} (W (p := p) (k := k)) ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : Coeff (p := p) (k := k) ≃+*
        W (p := p) (k := k)).toRingHom)

abbrev modulesEquivalence := SmallCrystallineTopologyAdapter.SmallCrystallineAdapter.sheafEquivalence (p := p) (k := k) (X := X)
  (ModuleCat.{u + 1} (Coeff (p := p) (k := k)))

instance modules65Grothendieck : IsGrothendieckAbelian.{u + 1}
    (Sheaf (SmallCrystallineTopologyAdapter.SmallCrystallineAdapter.topology65 (p := p) (k := k) (X := X)) (ModuleCat.{u + 1} (Coeff (p := p) (k := k)))) := by
  have : EssentiallySmall.{u + 1} (SmallCrystallineDpow.SmallCrystallineAdapter.Small65 (p := p) (k := k) (X := X)) := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1, u + 1, u, u + 2, u + 1}
    (SmallCrystallineTopologyAdapter.SmallCrystallineAdapter.topology65 (p := p) (k := k) (X := X)) (ModuleCat.{u + 1} (Coeff (p := p) (k := k)))

instance modules65EnoughInjectives : EnoughInjectives
    (Sheaf (SmallCrystallineTopologyAdapter.SmallCrystallineAdapter.topology65 (p := p) (k := k) (X := X)) (ModuleCat.{u + 1} (Coeff (p := p) (k := k)))) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

instance modulesEquivalence_additive :
    (modulesEquivalence (p := p) (k := k) (X := X)).functor.Additive where
  map_add := by intros; rfl

instance modulesEquivalence_linear :
    (modulesEquivalence (p := p) (k := k) (X := X)).functor.Linear (Coeff (p := p) (k := k)) where
  map_smul := by intros; rfl

abbrev structure65 := IntegralComparison.Crystalline.Site.AffineThickening.structureModuleSheaf (p := p)
  (δB := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (f := IntegralComparison.Witt.Crystalline.wittStructureMap p k X)

abbrev constant65 := IntegralComparison.Crystalline.Site.AffineThickening.constantBaseSheaf (p := p)
  (δB := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (f := IntegralComparison.Witt.Crystalline.wittStructureMap p k X)

def structureIso : (modulesEquivalence (p := p) (k := k) (X := X)).functor.obj structure65 ≅
    AlgebraicGeometry.Crystalline.Cohomology.Site.structureSheaf p k X :=
  (SmallCrystallineDpow.SmallCrystallineAdapter.to65.pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} (Coeff (p := p) (k := k))) SmallCrystallineTopologyAdapter.SmallCrystallineAdapter.topology62 SmallCrystallineTopologyAdapter.SmallCrystallineAdapter.topology65).symm.app largePresheaf65 ≪≫
      (presheafToSheaf SmallCrystallineTopologyAdapter.SmallCrystallineAdapter.topology62 (ModuleCat.{u + 1} (Coeff (p := p) (k := k)))).mapIso largePresheafIso

def constantIso : (modulesEquivalence (p := p) (k := k) (X := X)).functor.obj constant65 ≅
    AlgebraicGeometry.Crystalline.Cohomology.Site.coefficientSheaf p k X :=
  (SmallCrystallineDpow.SmallCrystallineAdapter.to65.pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} (Coeff (p := p) (k := k))) SmallCrystallineTopologyAdapter.SmallCrystallineAdapter.topology62 SmallCrystallineTopologyAdapter.SmallCrystallineAdapter.topology65).symm.app
      ((Functor.const _).obj (ModuleCat.of (Coeff (p := p) (k := k)) (Coeff (p := p) (k := k))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineSheafAdapter.SmallCrystallineAdapter

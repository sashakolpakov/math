import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ScalarSheaf
import OAI.AlgebraicGeometry.Comparison.Betti.AntiDolbeaultResolution

/-! # Anti Dolbeault -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Complex.AntiDolbeault

noncomputable section

/-! Complex-linear maps in the actual antiholomorphic Dolbeault resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

def complexAntiDolbeaultMap (q : ℕ) :
    DivisorClass.Chern.PureManifoldDolbeaultSheaf.antiOpenManifoldFormSheaf E M q ⟶ DivisorClass.Chern.PureManifoldDolbeaultSheaf.antiOpenManifoldFormSheaf E M (q + 1) :=
  ObjectProperty.homMk {
    app U := ModuleCat.ofHom (DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD U.unop q)
    naturality := by
      intro U V i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact (DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD_restrict (leOfHom i.unop) a).symm }

theorem complexAntiDolbeaultMap_forget (q : ℕ) :
    (Holomorphic.ScalarSheaf.Dolbeault.complexSheafForget M).map (complexAntiDolbeaultMap E M q) =
      DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M q := rfl

theorem complexAntiDolbeaultMap_squared (q : ℕ) :
    complexAntiDolbeaultMap E M q ≫ complexAntiDolbeaultMap E M (q + 1) = 0 := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD_squared U.unop q a

def complexAntiDolbeaultComplex :
    CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M)) ℕ :=
  CochainComplex.of (DivisorClass.Chern.PureManifoldDolbeaultSheaf.antiOpenManifoldFormSheaf E M) (complexAntiDolbeaultMap E M)
    (complexAntiDolbeaultMap_squared E M)

def holomorphicToComplexAntiZero :
    Holomorphic.ScalarSheaf.Dolbeault.holomorphicScalarSheaf E M ⟶ DivisorClass.Chern.PureManifoldDolbeaultSheaf.antiOpenManifoldFormSheaf E M 0 :=
  ObjectProperty.homMk {
    app U := ModuleCat.ofHom (DivisorClass.Chern.ManifoldDolbeaultZeroKernel.pureHolomorphicManifoldZeroFormLinear U.unop)
    naturality := by
      intro U V i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro g
      apply Subtype.ext
      exact (DivisorClass.Chern.Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_restrict (leOfHom i.unop) g
        ((DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M).obj.map i g) (fun _ => rfl)).symm }

theorem holomorphicToComplexAntiZero_forget :
    (Holomorphic.ScalarSheaf.Dolbeault.complexSheafForget M).map (holomorphicToComplexAntiZero E M) =
      DivisorClass.Chern.ManifoldDolbeaultZeroKernel.holomorphicToPureManifoldZeroFormSheaf := rfl

theorem holomorphicToComplexAntiZero_mono : Mono (holomorphicToComplexAntiZero E M) := by
  apply (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro U
  exact (ModuleCat.mono_iff_injective _).mpr (DivisorClass.Chern.ManifoldDolbeaultZeroKernel.pureHolomorphicManifoldZeroFormLinear_injective U.unop)

theorem holomorphicToComplexAntiZero_d :
    holomorphicToComplexAntiZero E M ≫ complexAntiDolbeaultMap E M 0 = 0 := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  exact DivisorClass.Chern.ManifoldDolbeaultZeroKernel.pureHolomorphicManifoldZeroFormLinear_d U.unop g

def complexAntiDolbeaultSequence (q : ℕ) :
    ShortComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M)) :=
  ShortComplex.mk (complexAntiDolbeaultMap E M q) (complexAntiDolbeaultMap E M (q + 1))
    (complexAntiDolbeaultMap_squared E M q)

def holomorphicComplexAntiZeroSequence :
    ShortComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M)) :=
  ShortComplex.mk (holomorphicToComplexAntiZero E M) (complexAntiDolbeaultMap E M 0)
    (holomorphicToComplexAntiZero_d E M)

variable [FiniteDimensional ℂ E]

theorem complexAntiDolbeaultSequence_exact (q : ℕ) :
    (complexAntiDolbeaultSequence E M q).Exact := by
  exact @Functor.reflects_exact_of_faithful
    (TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M)) _ _
    (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M)) _ _
    (Holomorphic.ScalarSheaf.Dolbeault.complexSheafForget M) ⟨fun _ _ => rfl⟩ (Holomorphic.ScalarSheaf.Dolbeault.complexSheafForget_faithful M)
    (complexAntiDolbeaultSequence E M q) (AntiDolbeaultSheafExactness.antiManifoldDolbeaultSequence_exact E M q)

theorem holomorphicComplexAntiZeroSequence_exact :
    (holomorphicComplexAntiZeroSequence E M).Exact := by
  exact @Functor.reflects_exact_of_faithful
    (TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M)) _ _
    (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M)) _ _
    (Holomorphic.ScalarSheaf.Dolbeault.complexSheafForget M) ⟨fun _ _ => rfl⟩ (Holomorphic.ScalarSheaf.Dolbeault.complexSheafForget_faithful M)
    (holomorphicComplexAntiZeroSequence E M)
    DivisorClass.Chern.ManifoldDolbeaultZeroKernel.pureHolomorphicManifoldDolbeaultZeroSequence_exact

end

end OAI.AlgebraicGeometry.Comparison.Betti.Complex.AntiDolbeault

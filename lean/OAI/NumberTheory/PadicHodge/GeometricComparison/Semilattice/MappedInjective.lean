import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.MappedChartTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactInjectiveResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionHomotopy

/-! # Mapped Injective -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.MappedInjective.SemilatticeMappedInjectiveComparison

noncomputable section

/-! The chart cone gives the original augmentation-preserving map
to an exactly restricted injective resolution. Its induced map is
independent of any other augmented comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z t
variable (C : Type u) [SemilatticeInf C] {ι : Type} [Finite ι]
  (U : ι → C) (V : C)
  {A : Type v} [Category.{w} A] [Abelian A]
  [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type z} [Category.{t} B] [Abelian B]
  [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesInjectiveObjects] (P : Cᵒᵖ ⥤ CochainComplex A ℕ)
  (h : ∀ T : C, IsIso ((F.mapHomologicalComplex (.up ℕ)).map
    (P.map (homOfLE (inf_le_left : T ⊓ V ≤ T)).op)))
  {Z : A} (η : (Functor.const Cᵒᵖ).obj ((CochainComplex.single₀ A).obj Z) ⟶ P)
  {K : CochainComplex A ℕ} (e : K ≅ CechCone.Total.CechConeTotal.total U P)
  (a : (CochainComplex.single₀ A).obj Z ⟶ K)
  (ha : a ≫ e.hom = CechCone.Total.CechConeTotal.augmentation U P ((CochainComplex.single₀ A).obj Z) η)
  (J : InjectiveResolution Z) (b : K ⟶ J.cocomplex) (hb : a ≫ b = J.ι)

local notation "G" => F.mapHomologicalComplex (ComplexShape.up ℕ)

def augmentation : (CochainComplex.single₀ B).obj (F.obj Z) ⟶ (G).obj (P.obj (op V)) :=
  (IntegralComparison.ExactInjectiveResolution.sourceIso F).inv ≫ (G).map (η.app (op V))

def map : (G).obj (P.obj (op V)) ⟶ (IntegralComparison.ExactInjectiveResolution.map F J).cocomplex :=
  (MappedChartTotal.SemilatticeMappedChartTotal.map C U V F P h ≫ (G).map e.inv) ≫ (G).map b

include ha hb in
theorem augmentation_map : augmentation C V F P η ≫ SemilatticeMappedInjectiveComparison.map C U V F P h e J b =
    (IntegralComparison.ExactInjectiveResolution.map F J).ι := by
  have hchart := MappedChartTotal.SemilatticeMappedChartTotal.factorization_through_iso
    C U V F P h ((CochainComplex.single₀ A).obj Z) η e a ha
  change ((IntegralComparison.ExactInjectiveResolution.sourceIso F).inv ≫ (G).map (η.app (op V))) ≫
    ((MappedChartTotal.SemilatticeMappedChartTotal.map C U V F P h ≫ (G).map e.inv) ≫ (G).map b) =
      (IntegralComparison.ExactInjectiveResolution.sourceIso F).inv ≫ (G).map J.ι
  rw [Category.assoc, ← Category.assoc ((G).map (η.app (op V))), hchart,
    ← CategoryTheory.Functor.map_comp, hb]

variable [QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map (η.app (op V)))]

instance augmentation_quasiIso : QuasiIso (augmentation C V F P η) := by
  dsimp only [augmentation]
  infer_instance

def homotopy (c : (G).obj (P.obj (op V)) ⟶ (IntegralComparison.ExactInjectiveResolution.map F J).cocomplex)
    (hc : augmentation C V F P η ≫ c = (IntegralComparison.ExactInjectiveResolution.map F J).ι) :
    Homotopy (SemilatticeMappedInjectiveComparison.map C U V F P h e J b) c :=
  IntegralComparison.Augmented.ResolutionHomotopy.homotopy _ (augmentation C V F P η)
    (IntegralComparison.ExactInjectiveResolution.map F J) _ c
    ((augmentation_map C U V F P h η e a ha J b hb).trans hc.symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.MappedInjective.SemilatticeMappedInjectiveComparison

import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorCechComplex

/-! # Tensor Cech Tmul -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorCechTmul.Construction

noncomputable section

/-! A local section comparison compatible with restriction identifies the Cech complexes. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped TensorProduct

universe u

variable {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    {X Y : TopCat.{u}} (h : Y ⟶ X)
    (F : TopCat.Sheaf (ModuleCat.{u} R) X) (G : TopCat.Sheaf (ModuleCat.{u} K) Y)

structure TensorCechLocalComparison (P : Opens X → Prop) where
  sectionEquiv : ∀ W, P W → (K ⊗[R] F.obj.obj (op W)) ≃ₗ[K] G.obj.obj (op ((Opens.map h).obj W))
  restrict : ∀ {U V} (i : V ⟶ U) (hU : P U) (hV : P V) (z : K ⊗[R] F.obj.obj (op U)),
    sectionEquiv V hV ((F.obj.map i.op).hom.baseChange K z) =
      G.obj.map ((Opens.map h).map i).op (sectionEquiv U hU z)

namespace TensorCechLocalComparison

variable {h F G} {P : Opens X → Prop} (q : TensorCechLocalComparison h F G P)
    {ι : Type u} (U : ι → Opens X)
    (h₀ : ∀ i, P (U i)) (h₁ : ∀ i j, P (U i ⊓ U j))
    (h₂ : ∀ i j k, P ((U i ⊓ U j) ⊓ U k))

abbrev mappedOpens : ι → Opens Y := fun i ↦ (Opens.map h).obj (U i)

def coordinates0 : CechBaseChangeCoordinates.Construction.tensorCechC0 (K := K) F U ≃ₗ[K] OpenCechDegreeZero.Construction.openModuleCechC0 G (mappedOpens (h := h) U) :=
  LinearEquiv.piCongrRight fun i ↦ q.sectionEquiv (U i) (h₀ i)

def coordinates1 : CechBaseChangeCoordinates.Construction.tensorCechC1 (K := K) F U ≃ₗ[K] OpenCechDegreeZero.Construction.openModuleCechC1 G (mappedOpens (h := h) U) :=
  LinearEquiv.piCongrRight fun i ↦ LinearEquiv.piCongrRight fun j ↦ q.sectionEquiv _ (h₁ i j)

def coordinates2 : CechBaseChangeCoordinates.Construction.tensorCechC2 (K := K) F U ≃ₗ[K] OpenCechShortComplex.Construction.openModuleCechC2 G (mappedOpens (h := h) U) :=
  LinearEquiv.piCongrRight fun i ↦ LinearEquiv.piCongrRight fun j ↦ LinearEquiv.piCongrRight fun k ↦
    q.sectionEquiv _ (h₂ i j k)

theorem coordinates_d0 :
    (q.coordinates1 U h₁).toLinearMap.comp (TensorCechDifferentials.Construction.tensorCechD0 F U) =
      (OpenCechDegreeZero.Construction.openModuleCechD0 G (mappedOpens (h := h) U)).comp (q.coordinates0 U h₀).toLinearMap := by
  apply LinearMap.ext
  intro z
  funext i j
  change q.sectionEquiv _ (h₁ i j)
    ((F.obj.map (homOfLE inf_le_right : U i ⊓ U j ⟶ U j).op).hom.baseChange K (z j) -
      (F.obj.map (homOfLE inf_le_left : U i ⊓ U j ⟶ U i).op).hom.baseChange K (z i)) = _
  rw [map_sub]
  exact congrArg₂ (fun x y ↦ x - y)
    (q.restrict (homOfLE inf_le_right) (h₀ j) (h₁ i j) (z j))
    (q.restrict (homOfLE inf_le_left) (h₀ i) (h₁ i j) (z i))

theorem coordinates1_restrict (z : CechBaseChangeCoordinates.Construction.tensorCechC1 (K := K) F U) (i j : ι)
    (W : Opens X) (hW : P W) (hi : W ≤ U i) (hj : W ≤ U j) :
    q.sectionEquiv W hW (TensorCechDifferentials.Construction.tensorCechRestrict1 F U z i j W hi hj) =
      OpenCechCocycles.Construction.openCechRestrict1 G (mappedOpens (h := h) U) (q.coordinates1 U h₁ z) i j
        ((Opens.map h).obj W) ((Opens.map h).monotone hi) ((Opens.map h).monotone hj) :=
  q.restrict (homOfLE (le_inf hi hj)) (h₁ i j) hW (z i j)

theorem coordinates_d1 :
    (q.coordinates2 U h₂).toLinearMap.comp (TensorCechDifferentials.Construction.tensorCechD1 F U) =
      (OpenCechShortComplex.Construction.openModuleCechD1 G (mappedOpens (h := h) U)).comp (q.coordinates1 U h₁).toLinearMap := by
  apply LinearMap.ext
  intro z
  funext i j k
  change q.sectionEquiv _ (h₂ i j k)
    (TensorCechDifferentials.Construction.tensorCechRestrict1 F U z i j ((U i ⊓ U j) ⊓ U k)
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) +
    TensorCechDifferentials.Construction.tensorCechRestrict1 F U z j k ((U i ⊓ U j) ⊓ U k)
      (inf_le_left.trans inf_le_right) inf_le_right -
    TensorCechDifferentials.Construction.tensorCechRestrict1 F U z i k ((U i ⊓ U j) ⊓ U k)
      (inf_le_left.trans inf_le_left) inf_le_right) = _
  rw [map_sub, map_add]
  exact congrArg₂ (fun x y ↦ x - y)
    (congrArg₂ (fun x y ↦ x + y)
      (q.coordinates1_restrict U h₁ z i j _ (h₂ i j k)
        (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right))
      (q.coordinates1_restrict U h₁ z j k _ (h₂ i j k)
        (inf_le_left.trans inf_le_right) inf_le_right))
    (q.coordinates1_restrict U h₁ z i k _ (h₂ i j k)
      (inf_le_left.trans inf_le_left) inf_le_right)

variable [Fintype ι] [DecidableEq ι]

def complexIso :
    ModuleBaseChangeComplex.Construction.moduleBaseChangeComplex R K (OpenCechShortComplex.Construction.openModuleCechShortComplex F U) ≅
      OpenCechShortComplex.Construction.openModuleCechShortComplex G (mappedOpens (h := h) U) :=
  TensorCechComplex.Construction.tensorCechComplexIso F U ≪≫ ShortComplex.isoMk
    (q.coordinates0 U h₀).toModuleIso
    (q.coordinates1 U h₁).toModuleIso
    (q.coordinates2 U h₂).toModuleIso
    (by apply ModuleCat.hom_ext; exact (q.coordinates_d0 U h₀ h₁).symm)
    (by apply ModuleCat.hom_ext; exact (q.coordinates_d1 U h₁ h₂).symm)

theorem complexIso_first_tmul (a : K) (z : OpenCechDegreeZero.Construction.openModuleCechC0 F U) (i : ι) :
    (q.complexIso U h₀ h₁ h₂).hom.τ₁ (a ⊗ₜ[R] z) i =
      q.sectionEquiv (U i) (h₀ i) (a ⊗ₜ[R] z i) := rfl

theorem complexIso_middle_tmul (a : K) (z : OpenCechDegreeZero.Construction.openModuleCechC1 F U) (i j : ι) :
    (q.complexIso U h₀ h₁ h₂).hom.τ₂ (a ⊗ₜ[R] z) i j =
      q.sectionEquiv (U i ⊓ U j) (h₁ i j) (a ⊗ₜ[R] z i j) := rfl

end TensorCechLocalComparison

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorCechTmul.Construction

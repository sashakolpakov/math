import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechAdditiveCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.EdgeCoefficient
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.SingleEdge

/-! # Edge Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.EdgeCoordinates.Intrinsic

noncomputable section

/-! The original native ordered global edge and its literal additive
presheaf edge agree under the checked coefficient coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
  (K : CochainComplex X.Modules ℕ)

local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CoefficientQuasiIso.coefficients π K

def sectionMap (M : X.Modules) : (OrderedCech.Augmentation.sections π).obj M ⟶
    (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (Opposite.op ⊤) :=
  ModuleCat.ofHom (X := (OrderedCech.Augmentation.sections π).obj M)
    (Y := (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (Opposite.op ⊤))
    (AlgebraicGeometry.SheafCohomology.Projective.BaseGlobalRestriction.baseGlobalRestriction π M ⊤)

omit [X.IsSeparated] in
@[simp] theorem sectionMap_apply (M : X.Modules) (x : (OrderedCech.Augmentation.sections π).obj M) :
    sectionMap π M x = x := by
  change M.presheaf.map ((homOfLE (le_refl (⊤ : X.Opens))).op) x = x
  have h : (homOfLE (le_refl (⊤ : X.Opens))).op = 𝟙 (Opposite.op (⊤ : X.Opens)) := rfl
  rw [h, M.presheaf.map_id]
  rfl

def sectionsMap : OrderedCech.Total.Comparison.sectionComplex π K ⟶
    Presheaf.OrderedCechEdge.sections P where
  f q := sectionMap π (K.X q)
  comm' q r _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (congrArg (fun y => ((K.d q r).val.app (Opposite.op ⊤)) y)
      (sectionMap_apply π (K.X q) x)).trans
        (sectionMap_apply π (K.X r) (((K.d q r).val.app (Opposite.op ⊤)) x)).symm

omit [X.IsSeparated] in
theorem augmentation (M : X.Modules) :
    OrderedCech.Augmentation.map π U M = sectionMap π M ≫
      Presheaf.OrderedCechEdge.augmentation U (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M) := by
  apply Pi.hom_ext
  intro j
  have ha := Presheaf.OrderedCechEdge.augmentation_projection U
    (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M) j
  have hb := OrderedCech.Augmentation.map_π π U M j
  refine hb.trans ?_
  rw [Category.assoc]
  refine (Eq.trans ?_ (congrArg (sectionMap π M ≫ ·) ha.symm))
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun y => M.presheaf.map
    (homOfLE (le_top : (∏ᶜ fun k : Fin 1 => U (j.val k)) ≤ (⊤ : X.Opens))).op y)
      (sectionMap_apply π M x).symm

omit [X.IsSeparated] in
theorem linear :
    OrderedCech.Total.Comparison.edge π U K hU ≫
      (CechTotalCoordinates.Intrinsic.iso π U K).inv =
    sectionsMap π K ≫ Presheaf.OrderedCechEdge.edge U P := by
  let b := ((NatIso.mapHomologicalComplex (CechCoordinates.Intrinsic.functorIso π U)
    (.up ℕ)).app K).inv
  exact BicomplexHorizontalEdge.naturality
    (OrderedCech.Total.Comparison.bicomplex π U K) (OrderedCech.Total.Comparison.sectionComplex π K)
    (fun q => OrderedCech.Augmentation.map π U (K.X q))
    (fun q q' _ => (OrderedCech.Augmentation.naturality π U (K.d q q')).symm)
    (fun q => OrderedCech.Augmentation.map_d π U (K.X q) hU)
    (Presheaf.OrderedCechEdge.bicomplex U P) (Presheaf.OrderedCechEdge.sections P)
    (fun q => Presheaf.OrderedCechEdge.augmentation U ((P).X q))
    (fun q q' _ => Presheaf.OrderedCechEdge.augmentation_comm U P q q')
    (Presheaf.OrderedCechEdge.augmentation_cocycle U P) b (sectionsMap π K) (fun q => by
      change OrderedCech.Augmentation.map π U (K.X q) ≫ 𝟙 _ = _
      rw [Category.comp_id]
      exact augmentation π U (K.X q))

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.forgetScalars (S := S)
local instance finiteBiproducts : HasFiniteBiproducts (ModuleCat.{u} Γ(S, ⊤)) :=
  Abelian.hasFiniteBiproducts

abbrev mapped_linear := by
  let F := (G).mapHomologicalComplex (.up ℕ)
  have h := congrArg F.map (linear π U hU K)
  rw [F.map_comp, F.map_comp] at h
  exact h

omit [X.IsSeparated] in
theorem forget_sectionsMap :
    ((G).mapHomologicalComplex (.up ℕ)).map (sectionsMap π K) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply AddCommGrpCat.hom_ext
  ext x
  exact sectionMap_apply π (K.X q) x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.EdgeCoordinates.Intrinsic

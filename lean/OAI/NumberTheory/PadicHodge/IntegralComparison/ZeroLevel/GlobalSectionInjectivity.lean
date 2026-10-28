import OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.GlobalFunctions
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Covering

/-! # Global Section Injectivity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.GlobalSectionInjectivity

noncomputable section

/-! Smoothness makes the actual global-function value of a level-zero crystalline section injective. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.AffineOpenSections

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [Smooth X.hom]

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

theorem value_eq_of_support (s t : AffineOpenSections.Sections p k X) (V : X.left.Opens) (hV : IsAffineOpen V)
    (h : AffineOpenSections.value p k X s V hV = AffineOpenSections.value p k X t V hV)
    (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (Witt.Crystalline.wittStructureMap p k X) 0)
    (hr : Set.range U.obj.mapToX ⊆ Set.range hV.fromSpec) : s.app (op U) = t.app (op U) := by
  let j : Spec (CommRingCat.of (U.obj.ring ⧸ U.obj.ideal)) ⟶ Spec Γ(X.left, V) :=
    IsOpenImmersion.lift hV.fromSpec U.obj.mapToX hr
  have hj : j ≫ hV.fromSpec = U.obj.mapToX := IsOpenImmersion.lift_fac hV.fromSpec U.obj.mapToX hr
  obtain ⟨β⟩ := @OpenFrame.exists_map p inferInstance k (AffineOpenSections.sectionRing k X V)
    inferInstance inferInstance inferInstance (CommAlgCat.commRing (AffineOpenSections.sectionRing k X V))
    (CommAlgCat.algebra (AffineOpenSections.sectionRing k X V)) X hV.fromSpec
    (AffineOpen.SectionBase.overBase k X V hV) U.obj j hj (AffineOpenSections.smooth k X V hV)
    ((pow_one (p : U.obj.ring)).symm.trans U.property)
  let γ : U ⟶ AffineOpenSections.frame p k X V hV := ObjectProperty.homMk β
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  apply ULift.ext
  exact (BoundedCrystalline.CrystallineSections.value_natural f 0 s γ).symm.trans
    ((congrArg β.ringMap h).trans (BoundedCrystalline.CrystallineSections.value_natural f 0 t γ))

theorem affine_ext (s t : AffineOpenSections.Sections p k X)
    (h : ∀ (U : X.left.Opens) (hU : IsAffineOpen U), AffineOpenSections.value p k X s U hU = AffineOpenSections.value p k X t U hU) : s = t := by
  have hP := (BoundedCrystalline.Site.inclusion (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0).op_comp_isSheaf_of_isSheaf
      (BoundedCrystalline.Site.topology f 0) BigCrystallineSite.Object.topology
      (BigCrystallineCohomology.largePresheaf f) (Crystalline.StructureDescent.largePresheaf_isSheaf f)
  apply NatTrans.ext
  funext T
  let V : X.left.affineOpens → X.left.Opens := fun U => U.val
  have hc : BoundedOpen.Covering.sieve V T.unop ∈ BoundedCrystalline.Site.topology f 0 T.unop := by
    apply BoundedOpen.Covering.covering
    intro z
    exact TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top X.left).symm ▸ (show T.unop.obj.mapToX z ∈ (⊤ : X.left.Opens) from trivial))
  apply (hP (ModuleCat.of R R) (BoundedOpen.Covering.sieve V T.unop) hc).isSeparatedFor.ext
  intro U α hα
  obtain ⟨i, hi⟩ := hα
  have hr : Set.range U.obj.mapToX ⊆ Set.range i.property.fromSpec := by
    rw [i.property.range_fromSpec]
    exact (BoundedOpen.Support.property_iff_range_subset f 0 U i.val).mp hi
  have hv : s.app (op U) = t.app (op U) :=
    value_eq_of_support p k X s t i.val i.property (h i.val i.property) U hr
  exact ((s.naturality α.op).symm.trans (Category.id_comp _)).trans
    (hv.trans ((t.naturality α.op).symm.trans (Category.id_comp _)).symm)

theorem injective [IsSeparated X.hom] : Function.Injective (GlobalFunctions.value p k X) := by
  intro s t h
  apply affine_ext p k X
  intro U hU
  exact (GlobalFunctions.restriction p k X s U hU).symm.trans
    ((congrArg (X.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) h).trans
      (GlobalFunctions.restriction p k X t U hU))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.GlobalSectionInjectivity

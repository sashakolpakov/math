import OAI.RepresentationTheory.Theta.Geometric.CechAxisFunctional
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback

/-! # Cech Axis Section Value -/

namespace OAI.RepresentationTheory.Theta.Geometric.CechAxisSectionValue

noncomputable section

/-! The cochain-axis functional restricts to the literal value of
the original global section along the rigidification axis. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

open OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction

universe u
variable {X S : Scheme.{u}} (π : X ⟶ S) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)

theorem axisSectionFunctional_restriction (W : X.Opens) (hW : (⊤ : S.Opens) ≤ s ⁻¹ᵁ W)
    (a : (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤)) :
    CechAxisFunctional.axisSectionFunctional π s hs M r W hW
      (M.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op a) =
      r.hom.app ⊤ (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback s M a) := by
  have h := AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.restrictedPullbackSection_restriction s M (show W ≤ ⊤ from le_top)
    (le_refl (⊤ : S.Opens)) (show (⊤ : S.Opens) ≤ s ⁻¹ᵁ ⊤ from le_rfl) hW a
  change ((Scheme.Modules.pullback s).obj M).presheaf.map (𝟙 (op ⊤))
    (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback s M a) = _ at h
  rw [CategoryTheory.Functor.map_id] at h
  exact congrArg (r.hom.app ⊤) h.symm

theorem cechAxisFunctional_augmentation {I : Type u} [LinearOrder I]
    (U : I → X.Opens) (i : I)
    (hi : (⊤ : S.Opens) ≤ s ⁻¹ᵁ AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0
      (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i))
    (a : (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤)) :
    CechAxisFunctional.cechAxisFunctional π s hs M r U i hi (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map π M U a) =
      r.hom.app ⊤ (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback s M a) := by
  have h := ConcreteCategory.congr_hom
    (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map_π π M U (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i)) a
  exact (congrArg (CechAxisFunctional.axisSectionFunctional π s hs M r _ hi) h).trans
    (axisSectionFunctional_restriction π s hs M r _ hi a)

end

end OAI.RepresentationTheory.Theta.Geometric.CechAxisSectionValue

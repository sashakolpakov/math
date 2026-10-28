import OAI.RepresentationTheory.Theta.Geometric.CechAxisFunctional
import OAI.RepresentationTheory.Theta.Geometric.RestrictedAxisBaseChange
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeFactors

/-! # Cech Axis Base Change -/

namespace OAI.RepresentationTheory.Theta.Geometric.CechAxisBaseChange

noncomputable section

/-! The actual Cech pullback carries the axis-normalization functional
to its scalar extension on the changed parameter scheme. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u
variable {X Y S T : Scheme.{u}}
    (f : Y ⟶ X) (b : T ⟶ Y) (g : T ⟶ S) (s : S ⟶ X) (h : b ≫ f = g ≫ s)
    {I : Type u} [LinearOrder I] (U : I → X.Opens) (i : I)

include g h in
theorem cechAxisOpen_baseChange
    (hi : (⊤ : S.Opens) ≤ s ⁻¹ᵁ AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0
      (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i)) :
    (⊤ : T.Opens) ≤ b ⁻¹ᵁ AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection (fun j => f ⁻¹ᵁ U j) 0
      (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i) := by
  intro x _
  have hx := hi (show g x ∈ (⊤ : S.Opens) from trivial)
  have he : f (b x) = s (g x) := congrArg (fun a : T ⟶ X => a x) h
  change b x ∈ AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection (fun j => f ⁻¹ᵁ U j) 0
    (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i)
  have ho : f ⁻¹ᵁ AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i) =
      AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection (fun j => f ⁻¹ᵁ U j) 0
        (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i) :=
    (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection f) U 0 (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i).1
  have hx' : f (b x) ∈ AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0
      (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i) := by
    rw [he]
    exact hx
  exact (congrArg (fun V : Y.Opens => b x ∈ V) ho).mp hx'

theorem cechAxisFunctional_restrictedBaseChange
    (π : X ⟶ S) (ρ : Y ⟶ T) (hπ : f ≫ π = ρ ≫ g)
    (hs : s ≫ π = 𝟙 S) (hb : b ≫ ρ = 𝟙 T)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (hi : (⊤ : S.Opens) ≤ s ⁻¹ᵁ AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0
      (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i)) (z : (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).X 0) :
    CechAxisFunctional.cechAxisFunctional ρ b hb ((Scheme.Modules.pullback f).obj M)
      (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r) (fun j => f ⁻¹ᵁ U j) i
      (cechAxisOpen_baseChange f b g s h U i hi)
        ((AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.restrictedMap f π ρ g hπ M U).f 0 z) =
      g.appTop (CechAxisFunctional.cechAxisFunctional π s hs M r U i hi z) := by
  let a := AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i
  let W := AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0 a
  let V := AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection (fun j => f ⁻¹ᵁ U j) 0 a
  have hV : V ≤ f ⁻¹ᵁ W := ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Hom.preimage_cechIntersection f) U 0 a.1).ge
  let q := Pi.π (fun j : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex I 0 => AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 j.1) a z
  have hc := ConcreteCategory.congr_hom
    (AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeComponents.Construction.CechBaseChangeMap.restricted_component_π f π ρ g hπ M U 0 a) z
  refine (congrArg (CechAxisFunctional.axisSectionFunctional ρ b hb ((Scheme.Modules.pullback f).obj M)
    (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r) V
      (cechAxisOpen_baseChange f b g s h U i hi)) hc).trans ?_
  have hf : AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeComponents.Construction.CechBaseChangeMap.factorMap f π ρ g hπ M U 0 a q =
      AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map f M W V hV q :=
    AlgebraicGeometry.Quotients.FiniteDescent.CechBaseChangeFactors.Construction.CechBaseChangeMap.factor_apply f π ρ g hπ M U 0 a q
  exact (congrArg (fun y => (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b g s h M r).hom.app ⊤
      (AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map b ((Scheme.Modules.pullback f).obj M) V ⊤
        (cechAxisOpen_baseChange f b g s h U i hi) y)) hf).trans
    (RestrictedAxisBaseChange.restrictedAxisValue_baseChange f b g s h M r W V hV hi
      (cechAxisOpen_baseChange f b g s h U i hi) q)

end

end OAI.RepresentationTheory.Theta.Geometric.CechAxisBaseChange

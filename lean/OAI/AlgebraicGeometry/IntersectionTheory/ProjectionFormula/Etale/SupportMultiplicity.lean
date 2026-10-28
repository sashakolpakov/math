import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.SupportTor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.ModuleSquare
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.PullbackModule
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Truncation

/-! # Support Multiplicity -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.SupportMultiplicity

noncomputable section

/-! Native geometric intersection Tor lengths are preserved by an
etale map of supports inside a smooth ambient morphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

theorem localTorLength {X Y : Scheme} [IsLocallyNoetherian Y] (f : X ⟶ Y) [Smooth f]
    [GeometricallyIntegral f] (A : IrreducibleCloseds X) (B C : IrreducibleCloseds Y)
    (g : CycleClass.Geometric.GenericPoint.reducedSupportScheme A ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme B)
    (h : CycleClass.Geometric.GenericPoint.reducedSupportι A ≫ f = g ≫ CycleClass.Geometric.GenericPoint.reducedSupportι B)
    (V : (CycleClass.Geometric.GenericPoint.reducedSupportScheme A).Opens) [Etale (V.ι ≫ g)]
    (x : X) (hxA : x ∈ (A : Set X)) (hxB : f x ∈ (B : Set Y)) (hxC : f x ∈ (C : Set Y))
    (hxV : CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA ∈ V) (i : ℕ) :
    CycleClass.Thom.IntersectionGeometry.localTorLength X (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport f C) A x (ProjectionFormula.Smooth.PullbackModule.mem f C x hxC) hxA i =
      CycleClass.Thom.IntersectionGeometry.localTorLength Y C B (f x) hxC hxB i := by
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  let T := (CycleClass.Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage B (f x) hxB)
  let U := (CycleClass.Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA)
  let θ := Support.ModuleSquare.map f A B g h x hxA hxB
  let : Algebra R S := (f.stalkMap x).hom.toAlgebra
  let : Algebra R T := (Local.Principal.supportStalkMap Y B (f x) hxB).hom.toAlgebra
  let : Algebra S U := (Local.Principal.supportStalkMap X A x hxA).hom.toAlgebra
  let : Algebra T U := θ.hom.toAlgebra
  let : Algebra R U := (Support.Stalk.Projection.map f A x hxA).hom.toAlgebra
  let : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R T U := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (Support.ModuleSquare.square f A B g h x hxA hxB)).symm
  let : Module.Flat R S := Flat.stalkMap f x
  have H := Support.ModuleSquare.Stalk.properties f A B g h x hxA hxB V hxV
  let : Module.Flat T U := H.1
  let : Algebra.FormallyUnramified T U := H.2.1
  let : Algebra.EssFiniteType T U := H.2.2
  let : IsLocalHom (algebraMap T U) := Support.ModuleSquare.Stalk.localHom f A B g h x hxA hxB
  have hRT : Function.Surjective (algebraMap R T) := Local.Principal.supportStalkMap_surjective Y B (f x) hxB
  have hSU : Function.Surjective (algebraMap S U) := Local.Principal.supportStalkMap_surjective X A x hxA
  let M := CycleClass.Thom.IntersectionGeometry.localSupportModule Y C (f x) hxC
  have he := Open.SupportTor.length_iso S (ProjectionFormula.Smooth.PullbackModule.equiv f C x hxC).symm.toModuleIso
    (Iso.refl (.of S U)) i
  exact he.trans (SupportTor.length R S T U hRT hSU Algebra.FormallyUnramified.map_maximalIdeal M i)

theorem multiplicity {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    [Smooth f.left] [GeometricallyIntegral (show X.carrier ⟶ Y.carrier from f.left)]
    (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
    (A D : IrreducibleCloseds X.carrier) (B C E : IrreducibleCloseds Y.carrier)
    (g : CycleClass.Geometric.GenericPoint.reducedSupportScheme A ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme B)
    (h : CycleClass.Geometric.GenericPoint.reducedSupportι A ≫ f.left = g ≫ CycleClass.Geometric.GenericPoint.reducedSupportι B)
    (V : (CycleClass.Geometric.GenericPoint.reducedSupportScheme A).Opens) [Etale (V.ι ≫ g)]
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint D ∈ (A : Set X.carrier))
    (hyB : CycleClass.Thom.IntersectionGeometry.supportPoint E ∈ (B : Set Y.carrier)) (hyC : CycleClass.Thom.IntersectionGeometry.supportPoint E ∈ (C : Set Y.carrier))
    (hxy : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint D) = CycleClass.Thom.IntersectionGeometry.supportPoint E)
    (hxV : CycleClass.Thom.IntersectionGeometry.supportPreimage A (CycleClass.Thom.IntersectionGeometry.supportPoint D) hxA ∈ V) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport (show X.carrier ⟶ Y.carrier from f.left) C) A D =
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity Y C B E := by
  let φ : X.carrier ⟶ Y.carrier := f.left
  have hxB : φ (CycleClass.Thom.IntersectionGeometry.supportPoint D) ∈ (B : Set Y.carrier) := hxy.symm ▸ hyB
  have hxC : φ (CycleClass.Thom.IntersectionGeometry.supportPoint D) ∈ (C : Set Y.carrier) := hxy.symm ▸ hyC
  have hxP := ProjectionFormula.Smooth.PullbackModule.mem φ C (CycleClass.Thom.IntersectionGeometry.supportPoint D) hxC
  rw [Truncation.intersectionMultiplicity_eq_relative_sum X m _ _ _ hxP hxA,
    Truncation.intersectionMultiplicity_eq_relative_sum Y n _ _ _ hyC hyB,
    ← Truncation.local_euler_sum_stable X m _ _ _ hxP hxA (m + n) (by omega),
    ← Truncation.local_euler_sum_stable Y n _ _ _ hyC hyB (m + n) (by omega)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact congrArg (fun l : ℕ∞ => (l.toNat : ℚ))
    ((localTorLength φ A B C g h V (CycleClass.Thom.IntersectionGeometry.supportPoint D) hxA hxB hxC hxV i).trans
      (Open.SupportTor.localTorLength_congr_point Y.carrier C B hxy hxC hxB hyC hyB i))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.SupportMultiplicity

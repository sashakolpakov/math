import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ClosedSupportCoordinates
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowMoving

/-! # Chart Germ -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm

noncomputable section

section

/-! Fixed finite ambient affine charts cover the chosen support.
Their native coordinate primes and section fractions are available
before any cycle is moved. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace FiniteSupportCharts

def affineMap {Y : Scheme} (U : Y.Opens) (hU : IsAffineOpen U) :
    Spec (.of (Γ(Y, U) : Type)) ⟶ Y := hU.fromSpec

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : IrreducibleCloseds X.carrier)

def Index : Type := {i : X.carrier.affineCover.finiteSubcover.I₀ //
  Nonempty ((CycleClass.Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ (X.carrier.affineCover.finiteSubcover.f i).opensRange)}

instance : Finite (Index X W) := by unfold Index; infer_instance

def opens (i : Index X W) : X.carrier.Opens :=
  (X.carrier.affineCover.finiteSubcover.f i.val).opensRange

theorem affine (i : Index X W) : IsAffineOpen (opens X W i) :=
  isAffineOpen_opensRange (X.carrier.affineCover.finiteSubcover.f i.val)

instance (i : Index X W) : Nonempty ((CycleClass.Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ opens X W i) := i.property

def ring (i : Index X W) : CommRingCat := Γ(X.carrier, opens X W i)

instance (i : Index X W) : IsNoetherianRing (ring X W i) :=
  IsLocallyNoetherian.component_noetherian ⟨opens X W i, affine X W i⟩

def chart (i : Index X W) : Spec (.of (ring X W i : Type)) ⟶ X.carrier :=
  affineMap (opens X W i) (affine X W i)

instance (i : Index X W) : IsOpenImmersion (chart X W i) := by unfold chart affineMap; infer_instance

def prime (i : Index X W) : PrimeSpectrum (ring X W i) :=
  ClosedSupportCoordinates.prime (CycleClass.Geometric.GenericPoint.reducedSupportι W) (opens X W i)

theorem prime_point (i : Index X W) : chart X W i (prime X W i) = CycleClass.Thom.IntersectionGeometry.supportPoint W :=
  (ClosedSupportCoordinates.point (CycleClass.Geometric.GenericPoint.reducedSupportι W) (opens X W i) (affine X W i)).trans
    (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W)

theorem prime_support (i : Index X W) :
    FiltrationAvoidance.support (chart X W i) (prime X W i) = W :=
  ClosedSupportCoordinates.support (CycleClass.Geometric.GenericPoint.reducedSupportι W) (opens X W i) (affine X W i)
    W (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W)

theorem covers (x : X.carrier) (hx : x ∈ (W : Set X.carrier)) :
    ∃ i : Index X W, x ∈ opens X W i := by
  obtain ⟨i, y, hy⟩ := X.carrier.affineCover.finiteSubcover.exists_eq x
  have hxi : x ∈ (X.carrier.affineCover.finiteSubcover.f i).opensRange := ⟨y, hy⟩
  have hnonempty : Nonempty ((CycleClass.Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ
      (X.carrier.affineCover.finiteSubcover.f i).opensRange) :=
    ⟨⟨CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx, by
      change CycleClass.Geometric.GenericPoint.reducedSupportι W (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx) ∈
        (X.carrier.affineCover.finiteSubcover.f i).opensRange
      rwa [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]⟩⟩
  exact ⟨⟨i, hnonempty⟩, hxi⟩

theorem exists_fractions (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    ∃ (a b : ∀ i : Index X W, ring X W i),
      (∀ i, a i ∉ (prime X W i).asIdeal ∧ b i ∉ (prime X W i).asIdeal) ∧
      ∀ (i : Index X W) (x : X.carrier) (hxW : x ∈ (W : Set X.carrier)) (hxU : x ∈ opens X W i),
        Support.LocalFraction.Restriction.toFunctionField X.carrier W x hxW
          (X.carrier.presheaf.germ (opens X W i) x hxU (a i)) ≠ 0 ∧
        Support.LocalFraction.Restriction.toFunctionField X.carrier W x hxW
          (X.carrier.presheaf.germ (opens X W i) x hxU (b i)) ≠ 0 ∧
        g = Support.LocalFraction.Restriction.toFunctionField X.carrier W x hxW
          (X.carrier.presheaf.germ (opens X W i) x hxU (a i)) /
          Support.LocalFraction.Restriction.toFunctionField X.carrier W x hxW
            (X.carrier.presheaf.germ (opens X W i) x hxU (b i)) := by
  choose a b ha hb he using fun i : Index X W =>
    SupportFractions.exists_sections X.carrier W (opens X W i) (affine X W i) g hg
  exact ⟨a, b, fun i => ⟨ha i, hb i⟩, he⟩

end FiniteSupportCharts

end

/-! An ambient affine section becomes exactly its native affine
stalk germ under the actual chart stalk isomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem map (X : Scheme) (U : X.Opens) (hU : IsAffineOpen U)
    (x : Spec Γ(X, U)) (hx : hU.fromSpec x ∈ U) :
    X.presheaf.germ U (hU.fromSpec x) hx ≫ hU.fromSpec.stalkMap x =
      StructureSheaf.toStalk Γ(X, U) x := by
  rw [Scheme.Hom.germ_stalkMap, hU.fromSpec_app_self, Category.assoc]
  rw [(Spec Γ(X, U)).presheaf.germ_res (eqToHom hU.fromSpec_preimage_self) x hx]
  rfl

theorem apply (X : Scheme) (U : X.Opens) (hU : IsAffineOpen U)
    (x : Spec Γ(X, U)) (hx : hU.fromSpec x ∈ U) (r : Γ(X, U)) :
    hU.fromSpec.stalkMap x (X.presheaf.germ U (hU.fromSpec x) hx r) =
      StructureSheaf.toStalk Γ(X, U) x r :=
  congrArg (fun f : Γ(X, U) ⟶ (Spec Γ(X, U)).presheaf.stalk x => f r) (map X U hU x hx)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm
